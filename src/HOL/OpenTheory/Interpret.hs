{- |
module: $Header$
description: OpenTheory interpretations
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.OpenTheory.Interpret
where

import Control.Monad (guard)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Text.Parsec ((<|>))
import qualified Text.Parsec as Parsec
import Text.Parsec.Text.Lazy ()
import Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as PP

import HOL.Name
import HOL.Parse
import HOL.Print

-------------------------------------------------------------------------------
-- Symbols
-------------------------------------------------------------------------------

data Symbol =
    TypeOpSymbol Name
  | ConstSymbol Name
  deriving (Eq,Ord,Show)

symbolName :: Symbol -> Name
symbolName (TypeOpSymbol n) = n
symbolName (ConstSymbol n) = n

renameSymbol :: Symbol -> Name -> Symbol
renameSymbol (TypeOpSymbol _) n = TypeOpSymbol n
renameSymbol (ConstSymbol _) n = ConstSymbol n

instance Printable Symbol where
  toDoc (TypeOpSymbol n) = PP.text "type" <+> quoteName n
  toDoc (ConstSymbol n) = PP.text "const" <+> quoteName n

instance Parsable Symbol where
  parser = do
      k <- kind
      space
      n <- parser
      return $ k n
    where
      kind = (Parsec.string "type" >> return TypeOpSymbol)
             <|> (Parsec.string "const" >> return ConstSymbol)

      space = Parsec.skipMany1 spaceParser

-------------------------------------------------------------------------------
-- Renaming a symbol
-------------------------------------------------------------------------------

data Rename = Rename Symbol Name
  deriving (Eq,Ord,Show)

destRename :: Rename -> (Symbol,Name)
destRename (Rename s n) = (s,n)

instance Printable Rename where
  toDoc (Rename s n) = toDoc s <+> PP.text "as" <+> quoteName n

instance Parsable Rename where
  parser = do
      s <- parser
      space
      _ <- Parsec.string "as"
      space
      n2 <- parser
      return $ Rename s n2
    where
      space = Parsec.skipMany1 spaceParser

-------------------------------------------------------------------------------
-- A collection of symbol renamings
-------------------------------------------------------------------------------

newtype Renames = Renames {destRenames :: [Rename]}
  deriving (Eq,Ord,Show)

instance Printable Renames where
  toDoc = PP.vcat . map toDoc . destRenames

instance Parsable Renames where
  parser = do
      Parsec.skipMany eolParser
      rs <- Parsec.sepEndBy line (Parsec.skipMany1 eolParser)
      return $ Renames (mapMaybe id rs)
    where
      line = comment <|> rename

      comment = do
        _ <- Parsec.char '#'
        Parsec.skipMany lineParser
        return Nothing

      rename = do
        r <- parser
        Parsec.skipMany spaceParser
        return $ Just r

concatRenames :: [Renames] -> Renames
concatRenames = Renames . concat . map destRenames

-------------------------------------------------------------------------------
-- Interpretations
-------------------------------------------------------------------------------

data Interpret = Interpret (Map Symbol Name)

mk :: Map Symbol Name -> Interpret
mk m = Interpret (Map.filterWithKey norm m)
  where
    norm s n = symbolName s /= n

empty :: Interpret
empty = mk Map.empty

toRenames :: Interpret -> Renames
toRenames (Interpret m) = Renames (map (uncurry Rename) (Map.toList m))

fromRenames :: Renames -> Maybe Interpret
fromRenames (Renames l) = do
    guard (Map.size m == length l)
    return (mk m)
  where
    m = Map.fromList $ map destRename l

fromRenamesUnsafe :: Renames -> Interpret
fromRenamesUnsafe r =
    case fromRenames r of
      Just i -> i
      Nothing -> error "HOL.OpenTheory.Interpret.fromRenames failed"

instance Printable Interpret where
  toDoc = toDoc . toRenames

instance Parsable Interpret where
  parser = fmap fromRenamesUnsafe parser

-------------------------------------------------------------------------------
-- Applying interpretations
-------------------------------------------------------------------------------

interpret :: Interpret -> Symbol -> Name
interpret (Interpret m) s =
    case Map.lookup s m of
      Just n -> n
      Nothing -> symbolName s

interpretTypeOp :: Interpret -> Name -> Name
interpretTypeOp i = interpret i . TypeOpSymbol

interpretConst :: Interpret -> Name -> Name
interpretConst i = interpret i . ConstSymbol

-------------------------------------------------------------------------------
-- Composing interpretations, should satisfy
--
-- |- interpret (compose i1 i2) s == interpret i2 (interpret i1 s)
-------------------------------------------------------------------------------

compose :: Interpret -> Interpret -> Interpret
compose i1 i2 = mk $ Map.foldrWithKey inc (dest i2) (dest i1)
  where
    dest (Interpret m) = m
    inc s1 n1 m2 = Map.insert s1 (interpret i2 (renameSymbol s1 n1)) m2

