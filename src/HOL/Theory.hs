{- |
module: $Header$
description: Higher order logic theories
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.Theory
where

import Control.Monad (guard)
import qualified Data.ByteString.Lazy as ByteString
import qualified Data.Char as Char
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.Encoding as Text.Encoding
import qualified HOL.Const as Const
--import qualified Text.ParserCombinators.Parsec
--import qualified Text.Parsec.ByteString.Lazy
import Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as PP

import HOL.Data
import HOL.Name
import HOL.Print
import HOL.Sequent (Sequent)
import qualified HOL.Sequent as Sequent
import qualified HOL.Term as Term
import qualified HOL.TermAlpha as TermAlpha
import HOL.Thm (Thm)
import qualified HOL.Thm as Thm
import qualified HOL.TypeOp as TypeOp

-------------------------------------------------------------------------------
-- Theories
-------------------------------------------------------------------------------

data Theory =
    Theory
      {typeOps :: Map Name TypeOp,
       consts :: Map Name Const,
       thms :: Map Sequent Thm}
  deriving (Eq,Ord,Show)

-------------------------------------------------------------------------------
-- Constructors and destructors
-------------------------------------------------------------------------------

empty :: Theory
empty = Theory {typeOps = Map.empty, consts = Map.empty, thms = Map.empty}

fromThmSet :: Set Thm -> Theory
fromThmSet th =
    Theory {typeOps = ts, consts = cs, thms = ths}
  where
    mk f = Map.fromList . map (\x -> (f x, x)) . Set.toList
    ts = mk TypeOp.name $ TypeOp.ops th
    cs = mk Const.name $ Const.consts th
    ths = mk Thm.dest th

-------------------------------------------------------------------------------
-- Symbols
-------------------------------------------------------------------------------

typeOpsList :: [Theory] -> Map Name (Set TypeOp)
typeOpsList =
    foldr add Map.empty
  where
    add thy ts = merge (typeOps thy) ts
    merge = Map.mergeWithKey combine only1 id
    combine _ t ts = Just (Set.insert t ts)
    only1 = Map.map Set.singleton

constsList :: [Theory] -> Map Name (Set Const)
constsList =
    foldr add Map.empty
  where
    add thy ts = merge (consts thy) ts
    merge = Map.mergeWithKey combine only1 id
    combine _ t ts = Just (Set.insert t ts)
    only1 = Map.map Set.singleton

-------------------------------------------------------------------------------
-- Union
-------------------------------------------------------------------------------

union :: Theory -> Theory -> Theory
union thy1 thy2 =
    Theory {typeOps = t, consts = c, thms = th}
  where
    Theory {typeOps = t1, consts = c1, thms = th1} = thy1
    Theory {typeOps = t2, consts = c2, thms = th2} = thy2
    t = Map.union t1 t2
    c = Map.union c1 c2
    th = Map.union th1 th2

unionList :: [Theory] -> Theory
unionList = foldr union empty

-------------------------------------------------------------------------------
-- Numbers
-------------------------------------------------------------------------------

type Number = Integer

parseNumber :: String -> Maybe Number
parseNumber =
    number
  where
    number [] = Nothing
    number ['0'] = Just 0
    number ('-' : s) = fmap negate $ positive s
    number s = positive s

    positive [] = Nothing
    positive ('0' : _) = Nothing
    positive s = digits 0 s

    digits z [] = Just z
    digits z (c : cs) = do
      guard (Char.isDigit c)
      let d = toInteger $ Char.digitToInt c
      digits (z * 10 + d) cs

-------------------------------------------------------------------------------
-- Objects
-------------------------------------------------------------------------------

data Object =
    NumObject Number
  | NameObject Name
  | ListObject [Object]
  | TypeOpObject TypeOp
  | TypeObject Type
  | ConstObject Const
  | VarObject Var
  | TermObject Term
  | ThmObject Thm
  deriving (Eq,Ord,Show)

termObject :: Object -> Maybe Term
termObject (TermObject tm) = Just tm
termObject _ = Nothing

sequentObject :: [Object] -> Term -> Maybe Sequent
sequentObject hl c = do
  h <- mapM termObject hl
  Sequent.mk (Set.fromList $ map TermAlpha.mk h) (TermAlpha.mk c)

-------------------------------------------------------------------------------
-- Commands
-------------------------------------------------------------------------------

data Command =
  -- Special commands
    NumCommand Number
  | NameCommand Name
  -- Regular commands
  | AbsTermCommand
  | AbsThmCommand
  | AppTermCommand
  | AppThmCommand
  | AssumeCommand
  | AxiomCommand
  | BetaConvCommand
  | ConsCommand
  | ConstCommand
  | ConstTermCommand
  | DeductAntisymCommand
  | DefCommand
  | DefineConstCommand
  | DefineConstListCommand
  | DefineTypeOpCommand
  | EqMpCommand
  | HdTlCommand
  | NilCommand
  | OpTypeCommand
  | PopCommand
  | PragmaCommand
  | ProveHypCommand
  | RefCommand
  | ReflCommand
  | RemoveCommand
  | SubstCommand
  | SymCommand
  | ThmCommand
  | TransCommand
  | TypeOpCommand
  | VarCommand
  | VarTermCommand
  | VarTypeCommand
  | VersionCommand
  -- Legacy commands
  | DefineTypeOpLegacyCommand
  deriving (Eq,Ord,Show)

regularCommands :: [(Command,String)]
regularCommands =
    [(AbsTermCommand,"absTerm"),
     (AbsThmCommand,"absThm"),
     (AppTermCommand,"appTerm"),
     (AppThmCommand,"appThm"),
     (AssumeCommand,"assume"),
     (AxiomCommand,"axiom"),
     (BetaConvCommand,"betaConv"),
     (ConsCommand,"cons"),
     (ConstCommand,"const"),
     (ConstTermCommand,"constTerm"),
     (DeductAntisymCommand,"deductAntisym"),
     (DefCommand,"def"),
     (DefineConstCommand,"defineConst"),
     (DefineConstListCommand,"defineConstList"),
     (DefineTypeOpCommand,"defineTypeOp"),
     (EqMpCommand,"eqMp"),
     (HdTlCommand,"hdTl"),
     (NilCommand,"nil"),
     (OpTypeCommand,"opType"),
     (PopCommand,"pop"),
     (PragmaCommand,"pragma"),
     (ProveHypCommand,"proveHyp"),
     (RefCommand,"ref"),
     (ReflCommand,"refl"),
     (RemoveCommand,"remove"),
     (SubstCommand,"subst"),
     (SymCommand,"sym"),
     (ThmCommand,"thm"),
     (TransCommand,"trans"),
     (TypeOpCommand,"typeOp"),
     (VarCommand,"var"),
     (VarTermCommand,"varTerm"),
     (VarTypeCommand,"varType"),
     (VersionCommand,"version")]

instance Printable Command where
  toDoc =
      go
    where
      m = Map.fromList $ map (\(c,s) -> (c, PP.text s)) regularCommands

      go (NumCommand i) = PP.integer i
      go (NameCommand n) = toDoc n
      go DefineTypeOpLegacyCommand = legacy DefineTypeOpCommand
      go c = case Map.lookup c m of
               Just d -> d
               Nothing -> error $ "Unprintable command: " ++ show c

      legacy c = go c <+> PP.text "(legacy)"

parseCommand :: String -> Maybe Command
parseCommand =
    regular
  where
    m = Map.fromList $ map (\(c,s) -> (s,c)) regularCommands

    regular s =
       case Map.lookup s m of
         Just c -> Just c
         Nothing -> special s

    special s =
       case parseName s of
         Just n -> Just $ NameCommand n
         Nothing -> fmap NumCommand $ parseNumber s

-------------------------------------------------------------------------------
-- OpenTheory article file versions
-------------------------------------------------------------------------------

type Version = Number

supportedCommand :: Version -> Command -> Bool
supportedCommand 5 DefineConstListCommand = False
supportedCommand 5 DefineTypeOpCommand = False
supportedCommand 5 HdTlCommand = False
supportedCommand 5 PragmaCommand = False
supportedCommand 5 ProveHypCommand = False
supportedCommand 5 SymCommand = False
supportedCommand 5 TransCommand = False
supportedCommand 5 VersionCommand = False
supportedCommand 6 DefineTypeOpLegacyCommand = False
supportedCommand _ _ = True

versionCommand :: Version -> Command -> Maybe Command
versionCommand 5 DefineTypeOpCommand = Just DefineTypeOpLegacyCommand
versionCommand _ VersionCommand = Nothing
versionCommand v c = if supportedCommand v c then Just c else Nothing

-------------------------------------------------------------------------------
-- Execution state
-------------------------------------------------------------------------------

data State =
    State
      {stack :: [Object],
       dict :: Map Number Object,
       export :: Set Thm}
  deriving (Eq,Ord,Show)

initialState :: State
initialState =
    State
      {stack = [],
       dict = Map.empty,
       export = Set.empty}

toStringState :: State -> String
toStringState = show

executeCommand :: Theory -> State -> Command -> Maybe State
executeCommand thy state cmd =
    case (cmd, stack state) of
      (NumCommand i, s) -> Just $ state {stack = NumObject i : s}
      (NameCommand n, s) -> Just $ state {stack = NameObject n : s}
      (AbsTermCommand, TermObject b : VarObject v : s) -> do
        let tm = Term.mkAbs v b
        return $ state {stack = TermObject tm : s}
      (AbsThmCommand, ThmObject b : VarObject v : s) -> do
        th <- Thm.mkAbs v b
        return $ state {stack = ThmObject th : s}
      (AppTermCommand, TermObject x : TermObject f : s) -> do
        tm <- Term.mkApp f x
        return $ state {stack = TermObject tm : s}
      (AppThmCommand, ThmObject x : ThmObject f : s) -> do
        th <- Thm.mkApp f x
        return $ state {stack = ThmObject th : s}
      (AssumeCommand, TermObject tm : s) -> do
        th <- Thm.assume tm
        return $ state {stack = ThmObject th : s}
      (AxiomCommand, TermObject c : ListObject h : s) -> do
        sq <- sequentObject h c
        th <- Map.lookup sq (thms thy)
        return $ state {stack = ThmObject th : s}
      _ -> Nothing

-------------------------------------------------------------------------------
-- Reading an OpenTheory article file
-------------------------------------------------------------------------------

type LineNumber = Integer

readArticle :: Theory -> FilePath -> IO (Set Thm)
readArticle thy art = do
    bs <- ByteString.readFile art
    let txt = Text.Encoding.decodeUtf8 bs
    let ls = zipWith mkLine [1..] $ Text.lines txt
    let (v,cs) = getVersion $ map parse $ filter notComment ls
    let s = List.foldl' execute initialState $ map (version v) cs
    return $ export s
  where
    mkLine :: LineNumber -> Text -> (Integer,String)
    mkLine l t = (l, Text.unpack t)

    notComment (_, '#' : _) = False
    notComment _ = True

    parse :: (LineNumber,String) -> (LineNumber,Command)
    parse (l,s) =
        case parseCommand s of
          Just c -> (l,c)
          Nothing -> error $ err "unparseable command" l s

    getVersion :: [(LineNumber,Command)] -> (Version,[(LineNumber,Command)])
    getVersion ((l, NumCommand v) : (_,VersionCommand) : cs) =
        if v == 6 then (v,cs)
        else error $ err "bad version number" l (show v)
    getVersion cs = (5,cs)

    version :: Version -> (LineNumber,Command) -> (LineNumber,Command)
    version v (l,c) =
        case versionCommand v c of
          Just c' -> (l,c')
          Nothing -> error $ err "unsupported command" l e
                     where e = "command " ++ toString c ++
                               " not supported in version " ++ show v ++
                               " article files"

    execute :: State -> (LineNumber,Command) -> State
    execute s (l,c) =
        case executeCommand thy s c of
          Just s' -> s'
          Nothing -> error $ err e l (toStringState s)
                     where e = "couldn't execute command " ++ toString c

    err :: String -> LineNumber -> String -> String
    err e l s = e ++ " at line " ++ show l ++
                " of article file " ++ art ++ ":\n" ++ s

-------------------------------------------------------------------------------
-- A minimal theory containing the standard axioms
-------------------------------------------------------------------------------

standard :: Theory
standard = fromThmSet Thm.standardAxioms
