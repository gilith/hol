{- |
module: $Header$
description: OpenTheory packages
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.OpenTheory.Package
where

import Control.Concurrent (forkIO)
import Control.Concurrent.MVar (newEmptyMVar,putMVar,readMVar)
import Control.Monad (foldM,guard)
import qualified Data.Char as Char
import qualified Data.List as List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import System.FilePath ((</>),(<.>),takeDirectory)
import qualified System.Process
import Text.Parsec ((<|>))
import qualified Text.Parsec as Parsec
import Text.Parsec.Text.Lazy ()
import Text.PrettyPrint ((<>),(<+>),($+$))
import qualified Text.PrettyPrint as PP

import HOL.OpenTheory.Article (readArticle)
import HOL.OpenTheory.Interpret (Interpret)
import qualified HOL.OpenTheory.Interpret as Interpret
import HOL.Parse
import HOL.Print
import HOL.Theory (Theory)
import qualified HOL.Theory as Theory

-------------------------------------------------------------------------------
-- Package names
-------------------------------------------------------------------------------

newtype Name = Name {destName :: String}
  deriving (Eq,Ord,Show)

instance Printable Name where
  toDoc = PP.text . destName

instance Parsable Name where
  parser = do
      c <- component
      cs <- Parsec.many (Parsec.try (Parsec.char sep >> component))
      return $ Name (List.intercalate [sep] (c : cs))
    where
      component = do
          h <- Parsec.lower
          t <- Parsec.many (Parsec.lower <|> Parsec.digit)
          return (h : t)

      sep = '-'

-------------------------------------------------------------------------------
-- Package versions
-------------------------------------------------------------------------------

newtype Version = Version {destVersion :: String}
  deriving (Eq,Ord,Show)

instance Printable Version where
  toDoc = PP.text . destVersion

instance Parsable Version where
  parser = do
      cs <- Parsec.sepBy1 component (Parsec.char sep)
      return $ Version (List.intercalate [sep] cs)
    where
      component = Parsec.many1 Parsec.digit
      sep = '.'

-------------------------------------------------------------------------------
-- Packages are stored in repos as name-version
-------------------------------------------------------------------------------

data NameVersion = NameVersion {name :: Name, version :: Version}
  deriving (Eq,Ord,Show)

instance Printable NameVersion where
  toDoc (NameVersion n v) = toDoc n <> PP.char '-' <> toDoc v

instance Parsable NameVersion where
  parser = do
      n <- parser
      _ <- Parsec.char '-'
      v <- parser
      return $ NameVersion n v

-------------------------------------------------------------------------------
-- Information formatted as key: value
-------------------------------------------------------------------------------

data KeyValue = KeyValue Name String
  deriving (Eq,Ord,Show)

instance Printable KeyValue where
  toDoc (KeyValue k v) = toDoc k <> PP.char ':' <+> PP.text v

instance Parsable KeyValue where
  parser = do
      Parsec.skipMany spaceParser
      n <- parser
      Parsec.skipMany spaceParser
      _ <- Parsec.char ':'
      Parsec.skipMany spaceParser
      v <- Parsec.many lineParser
      return $ KeyValue n (List.dropWhileEnd Char.isSpace v)

printKeyValue :: Printable a => Name -> a -> KeyValue
printKeyValue n a = KeyValue n (toString a)

matchKeyValue :: Name -> KeyValue -> Maybe String
matchKeyValue n (KeyValue k v) = if k == n then Just v else Nothing

parseKeyValue :: Parsable a => Name -> KeyValue -> Maybe a
parseKeyValue n v = do
    s <- matchKeyValue n v
    a <- fromString s
    return a

-------------------------------------------------------------------------------
-- Package information
-------------------------------------------------------------------------------

newtype Info = Info {destInfo :: [KeyValue]}
  deriving (Eq,Ord,Show)

nullInfo :: Info -> Bool
nullInfo = null . destInfo

appendInfo :: Info -> Info -> Info
appendInfo (Info l) (Info l') = Info (l ++ l')

concatInfo :: [Info] -> Info
concatInfo = Info . concat . map destInfo

firstInfo :: (KeyValue -> Maybe a) -> Info -> Maybe (a,Info)
firstInfo f = g [] . destInfo
  where
    g _ [] = Nothing
    g l (h : t) = case f h of
                    Just a -> Just (a, Info (foldl (flip (:)) t l))
                    Nothing -> g (h : l) t

firstGetInfo :: [Info -> Maybe (a,Info)] -> Info -> Maybe (a,Info)
firstGetInfo [] _ = Nothing
firstGetInfo (f : fs) i =
    case f i of
      Nothing -> firstGetInfo fs i
      x -> x

mapGetInfo :: (a -> b) -> (Info -> Maybe (a,Info)) -> Info -> Maybe (b,Info)
mapGetInfo f g = let f0 (a,i) = (f a, i) in fmap f0 . g

maybeGetInfo :: (Info -> Maybe (a,Info)) -> Info -> (Maybe a, Info)
maybeGetInfo f i =
    case f i of
      Just (a,i') -> (Just a, i')
      Nothing -> (Nothing,i)

listGetInfo :: (Info -> Maybe (a,Info)) -> Info -> ([a], Info)
listGetInfo f = g []
  where
    g l i = case f i of
              Just (a,i') -> g (a : l) i'
              Nothing -> (l,i)

instance Printable Info where
  toDoc = PP.vcat . map toDoc . destInfo

instance Parsable Info where
  parser = fmap Info $ Parsec.endBy parser eolParser

class Informative a where
  toInfo :: a -> Info

  getInfo :: Info -> Maybe (a,Info)

  fromInfo :: Info -> Maybe a
  fromInfo i = do
      (a,i') <- getInfo i
      guard $ nullInfo i'
      return a

instance Informative a => Informative [a] where
  toInfo = concatInfo . map toInfo

  getInfo = Just . listGetInfo getInfo

instance (Informative a, Informative b) => Informative (a,b) where
  toInfo (a,b) = appendInfo (toInfo a) (toInfo b)

  getInfo i = do
      (a,i') <- getInfo i
      (b,i'') <- getInfo i'
      return ((a,b),i'')

-------------------------------------------------------------------------------
-- Package files
-------------------------------------------------------------------------------

newtype File = File {destFile :: FilePath}
  deriving (Eq,Ord,Show)

instance Printable File where
  toDoc = PP.doubleQuotes . PP.text . destFile

instance Parsable File where
  parser = do
      _ <- Parsec.char '"'
      f <- Parsec.many (Parsec.noneOf "\"\n")
      _ <- Parsec.char '"'
      return $ File f

-------------------------------------------------------------------------------
-- Interpretations
-------------------------------------------------------------------------------

data Interpretation =
    Interpret Interpret.Rename
  | Interpretation File
  deriving (Eq,Ord,Show)

instance Informative Interpretation where
  toInfo (Interpret i) = Info [printKeyValue (Name "interpret") i]
  toInfo (Interpretation f) = Info [printKeyValue (Name "interpretation") f]

  getInfo = firstGetInfo [getInterpret,getInterpretation]
    where
      getInterpret =
        mapGetInfo Interpret
          (firstInfo (parseKeyValue (Name "interpret")))

      getInterpretation =
        mapGetInfo Interpretation
          (firstInfo (parseKeyValue (Name "interpretation")))

readInterpretation :: FilePath -> [Interpretation] -> IO Interpret
readInterpretation dir ints = do
    rs <- mapM readRen ints
    return $ Interpret.fromRenamesUnsafe (Interpret.concatRenames rs)
  where
    readRen (Interpret r) = return $ Interpret.Renames [r]
    readRen (Interpretation f) = fromTextFile (dir </> destFile f)

-------------------------------------------------------------------------------
-- Theory blocks
-------------------------------------------------------------------------------

data Operation =
    Article File
  | Include {package :: NameVersion, checksum :: Maybe String}
  | Union
  deriving (Eq,Ord,Show)

data Block =
    Block
      {block :: Name,
       imports :: [Name],
       interpret :: [Interpretation],
       operation :: Operation}
  deriving (Eq,Ord,Show)

instance Informative Operation where
  toInfo (Article f) = Info [printKeyValue (Name "article") f]
  toInfo (Include p c) = Info (pv : cv)
    where
      pv = printKeyValue (Name "package") p
      cv = case c of
             Just s -> [KeyValue (Name "checksum") s]
             Nothing -> []
  toInfo Union = Info []

  getInfo =
      firstGetInfo [getArticle,getInclude,getUnion]
    where
      getArticle = mapGetInfo Article getArticleFile

      getInclude i = do
        (p,i') <- getPackage i
        let (c,i'') = maybeGetInfo getChecksum i'
        return (Include p c, i'')

      getUnion i = Just (Union,i)

      getArticleFile = firstInfo (parseKeyValue (Name "article"))
      getPackage = firstInfo (parseKeyValue (Name "package"))
      getChecksum = firstInfo (matchKeyValue (Name "checksum"))

mkBlock :: Name -> Info -> Maybe Block
mkBlock n info = do
    let (imp,info') = listGetInfo getImport info
    (int,op) <- fromInfo info'
    guard (op /= Union || null int)
    return $ Block n imp int op
  where
    getImport = firstInfo (parseKeyValue (Name "import"))

destBlock :: Block -> (Name,Info)
destBlock (Block n imp int op) =
    (n, appendInfo impInfo (toInfo (int,op)))
  where
    impInfo = Info (map (printKeyValue (Name "import")) imp)

instance Printable Block where
  toDoc b =
      (toDoc n <+> PP.lbrace) $+$
      PP.nest 2 (toDoc i) $+$
      PP.rbrace
    where
      (n,i) = destBlock b

instance Parsable Block where
  parser = do
      n <- opener
      i <- parser
      closer
      case mkBlock n i of
        Just b -> return b
        Nothing -> Parsec.parserFail "couldn't parse block"
    where
      opener = do
        Parsec.skipMany spaceParser
        n <- parser
        Parsec.skipMany spaceParser
        _ <- Parsec.char '{'
        Parsec.skipMany spaceParser
        eolParser
        return n

      closer = do
        Parsec.skipMany spaceParser
        _ <- Parsec.char '}'
        Parsec.skipMany spaceParser

-------------------------------------------------------------------------------
-- Packages
-------------------------------------------------------------------------------

data Package =
    Package
      {information :: Info,
       source :: [Block]}
  deriving (Eq,Ord,Show)

instance Printable Package where
  toDoc (Package i bs) =
      PP.vcat (List.intersperse (PP.text "") (toDoc i : map toDoc bs))

instance Parsable Package where
  parser = do
    Parsec.skipMany eolParser
    i <- parser
    Parsec.skipMany eolParser
    bs <- Parsec.sepEndBy parser (Parsec.skipMany1 eolParser)
    return $ Package i bs

requires :: Package -> [Name]
requires = fst . listGetInfo getRequires . information
  where
    getRequires = firstInfo (parseKeyValue (Name "requires"))

-------------------------------------------------------------------------------
-- Interface to the OpenTheory package repository
-------------------------------------------------------------------------------

packageFile :: FilePath -> Name -> FilePath
packageFile d (Name n) = d </> n <.> "thy"

opentheory :: [String] -> IO String
opentheory args = System.Process.readProcess "opentheory" args []

opentheoryDirectory :: String -> IO FilePath
opentheoryDirectory s = do
    dir <- opentheory ["info","--directory",s]
    return $ List.dropWhileEnd Char.isSpace dir

directory :: Name -> IO FilePath
directory = opentheoryDirectory . toString

directoryVersion :: NameVersion -> IO FilePath
directoryVersion = opentheoryDirectory . toString

-------------------------------------------------------------------------------
-- Dependencies between theory blocks
-------------------------------------------------------------------------------

newtype Blocks = Blocks {destBlocks :: [Block]}
  deriving (Eq,Ord,Show)

mkBlocks :: [Block] -> Blocks
mkBlocks bl = Blocks (check [] [] (Name "main"))
  where
    check st bs n =
        if any ((==) n . block) bs then bs
        else if notElem n st then add (n : st) bs (get n)
        else error $ "import cycle including theory block " ++ toString n

    add st bs b = b : foldl (check st) bs (imports b)

    get n =
        case filter ((==) n . block) bl of
          [] -> error $ "missing theory block " ++ toString n
          [b] -> b
          _ : _ : _ -> error $ "multiple theory blocks named " ++ toString n

-------------------------------------------------------------------------------
-- Reading one package
-------------------------------------------------------------------------------

readVersion :: Theory -> Interpret -> NameVersion -> IO Theory
readVersion thy int nv = do
    dir <- directoryVersion nv
    readPackageFile thy int (packageFile dir (name nv))

readPackageFile :: Theory -> Interpret -> FilePath -> IO Theory
readPackageFile thy int file = do
    pkg <- fromTextFile file
    readPackage thy int (takeDirectory file) pkg

readPackage :: Theory -> Interpret -> FilePath -> Package -> IO Theory
readPackage thy int dir pkg = readBlocks thy int dir (mkBlocks (source pkg))

readBlocks :: Theory -> Interpret -> FilePath -> Blocks -> IO Theory
readBlocks thy int dir (Blocks bs) = do
    vs <- foldM initT Map.empty bs
    mapM_ (forkIO . mkT vs) bs
    readMVar (getT vs (block (head bs)))
  where
    mkT vs b = do
        ts <- mapM (readMVar . getT vs) (imports b)
        t <- readBlock thy int dir ts b
        putMVar (getT vs (block b)) t

    getT vs n =
        case Map.lookup n vs of
          Just v -> v
          Nothing -> error $ "bad theory block " ++ show n

    initT vs b = do
        v <- newEmptyMVar
        return $ Map.insert (block b) v vs

readBlock :: Theory -> Interpret -> FilePath -> [Theory] -> Block -> IO Theory
readBlock envThy envInt dir impThys b = do
    blockInt <- readInterpretation dir (interpret b)
    let int = Interpret.compose blockInt envInt
    case operation b of
      Article f -> do
          ths <- readArticle thy int (dir </> destFile f)
          return $ Theory.fromThmSet ths
      Include {package = nv} -> readVersion thy int nv
      Union -> return impThy
  where
    thy = Theory.union envThy impThy
    impThy = Theory.unionList impThys

-------------------------------------------------------------------------------
-- Dependencies between packages
-------------------------------------------------------------------------------

newtype Requires = Requires (Map Name ([Name],FilePath,Blocks))

emptyRequires :: Requires
emptyRequires = Requires Map.empty

addRequires :: Requires -> Name -> IO Requires
addRequires = add
  where
    add (Requires m) n = fmap Requires $ check [] m n

    check st m n =
        if Map.member n m then return m
        else if notElem n st then pkg (n : st) m n
        else error $ "requires cycle including package " ++ toString n

    pkg st m n = do
        d <- directory n
        p <- fromTextFile (packageFile d n)
        let r = requires p
        let s = mkBlocks (source p)
        foldM (check st) (Map.insert n (r,d,s) m) r

fromListRequires :: [Name] -> IO Requires
fromListRequires = foldM addRequires emptyRequires

-------------------------------------------------------------------------------
-- Reading packages
-------------------------------------------------------------------------------

readList :: [Name] -> IO [Theory]
readList ns = do
    req <- mkReq
    vs <- foldM initT Map.empty req
    mapM_ (forkIO . mkT vs) req
    mapM (readMVar . getT vs) ns
  where
    mkReq = do
        Requires m <- fromListRequires ns
        return $ Map.toList m

    mkT vs (n,(r,d,s)) = do
        ts <- mapM (readMVar . getT vs) r
        let thy = Theory.unionList (Theory.standard : ts)
        t <- readBlocks thy Interpret.empty d s
        putMVar (getT vs n) t

    getT vs n =
        case Map.lookup n vs of
          Just v -> v
          Nothing -> error $ "bad package " ++ show n

    initT vs (n,_) = do
        v <- newEmptyMVar
        return $ Map.insert n v vs
