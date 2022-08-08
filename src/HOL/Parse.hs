{- |
module: $Header$
description: Parsing
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.Parse
where

import qualified Data.ByteString.Lazy as ByteString
import qualified Data.Char as Char
import qualified Data.List as List
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.Encoding as Text.Encoding
import Text.Parsec ((<|>),Parsec)
import qualified Text.Parsec as Parsec
import Text.Parsec.Text.Lazy ()

import HOL.Name

-------------------------------------------------------------------------------
-- Parsing whitespace
-------------------------------------------------------------------------------

spaceParser :: Parsec Text st ()
spaceParser = Parsec.oneOf " \t" >> return ()

eolParser :: Parsec Text st ()
eolParser = Parsec.char '\n' >> return ()

lineParser :: Parsec Text st Char
lineParser = Parsec.noneOf "\n"

-------------------------------------------------------------------------------
-- Parsable types
-------------------------------------------------------------------------------

class Parsable a where
  parser :: Parsec Text st a

  fromText :: Text -> Maybe a
  fromText t =
      case Parsec.parse (parser <* Parsec.eof) "" t of
        Left _ -> Nothing
        Right a -> Just a

  fromString :: String -> Maybe a
  fromString = fromText . Text.pack

  fromStringUnsafe :: String -> a
  fromStringUnsafe s =
      case fromString s of
        Just a -> a
        Nothing -> error $ "couldn't parse " ++ show s

  fromTextFile :: FilePath -> IO a
  fromTextFile file = do
      bs <- ByteString.readFile file
      let txt = Text.Encoding.decodeUtf8 bs
      case Parsec.parse (parser <* Parsec.eof) file txt of
        Left e -> error $ show e
        Right a -> return a

-------------------------------------------------------------------------------
-- Integers
-------------------------------------------------------------------------------

data ParseInteger =
    StartParseInteger
  | ZeroParseInteger
  | NegativeParseInteger
  | NonZeroParseInteger Bool !Integer
  | ErrorParseInteger

advanceParseInteger :: ParseInteger -> Char -> ParseInteger
advanceParseInteger = advance
  where
    advance StartParseInteger '0' = ZeroParseInteger
    advance StartParseInteger '-' = NegativeParseInteger
    advance StartParseInteger d | Char.isDigit d = positive d
    advance NegativeParseInteger '0' = ErrorParseInteger
    advance NegativeParseInteger d | Char.isDigit d = negative d
    advance (NonZeroParseInteger s n) d | Char.isDigit d = accumulate s n d
    advance _ _ = ErrorParseInteger

    positive = NonZeroParseInteger True . charToInteger

    negative = NonZeroParseInteger False . charToInteger

    accumulate s n d = NonZeroParseInteger s (10 * n + charToInteger d)

    charToInteger = toInteger . Char.digitToInt

endParseInteger :: ParseInteger -> Maybe Integer
endParseInteger ZeroParseInteger = Just 0
endParseInteger (NonZeroParseInteger s i) = Just (if s then i else (-i))
endParseInteger _ = Nothing

type FoldlParseInteger a =
    (ParseInteger -> Char -> ParseInteger) ->
    ParseInteger -> a -> ParseInteger

parseInteger :: FoldlParseInteger a -> a -> Maybe Integer
parseInteger f = endParseInteger . f advanceParseInteger StartParseInteger

instance Parsable Integer where
  parser = zero <|> negative <|> positive
    where
      zero = do
          _ <- Parsec.char '0'
          return 0

      negative = do
          _ <- Parsec.char '-'
          k <- positive
          return (-k)

      positive = do
          h <- positiveDigit
          t <- Parsec.many digit
          return (List.foldl' (\n d -> 10 * n + d) h t)

      digit = zero <|> positiveDigit

      positiveDigit = do
          d <- Parsec.oneOf "123456789"
          return (toInteger $ Char.digitToInt d)

  fromText = parseInteger Text.foldl'

  fromString = parseInteger List.foldl'

-------------------------------------------------------------------------------
-- Names
-------------------------------------------------------------------------------

instance Parsable Name where
  parser = do
      _ <- Parsec.char '"'
      cs <- components
      _ <- Parsec.char '"'
      return (Name (Namespace (init cs)) (last cs))
    where
      components = Parsec.sepBy1 component (Parsec.char '.')

      component = Parsec.many char

      char = Parsec.noneOf escapable <|> escapedChar

      escapedChar = do
          _ <- Parsec.char '\\'
          c <- Parsec.oneOf escapable
          return c

      escapable = "\"\\."
