{- |
module: $Header$
description: OpenTheory interface
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.OpenTheory
where

import Control.Monad (guard)
import qualified Data.ByteString.Lazy as ByteString
import qualified Data.Char as Char
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.Encoding as Text.Encoding
import qualified System.Process
import Text.Parsec ((<|>))
import qualified Text.Parsec as Parsec
import Text.Parsec.Text.Lazy ()
import Text.PrettyPrint ((<>),(<+>),($+$))
import qualified Text.PrettyPrint as PP

import HOL.Data
import HOL.Name
import HOL.Parse
import HOL.Print
import qualified HOL.Rule as Rule
import HOL.Sequent (Sequent)
import qualified HOL.Sequent as Sequent
import qualified HOL.Subst as Subst
import qualified HOL.Term as Term
import qualified HOL.TermAlpha as TermAlpha
import HOL.Theory (Theory)
import qualified HOL.Theory as Theory
import HOL.Thm (Thm)
import qualified HOL.Thm as Thm
import qualified HOL.Type as Type
import qualified HOL.TypeVar as TypeVar
import qualified HOL.Var as Var

-------------------------------------------------------------------------------
-- Numbers
-------------------------------------------------------------------------------

newtype Number = Number Integer
  deriving (Eq,Ord,Show)

instance Printable Number where
  toDoc (Number i) = PP.integer i

instance Parsable Number where
  parser = do
      i <- parser
      return (Number i)

  fromText = fmap Number . fromText

  fromString = fmap Number . fromString

-------------------------------------------------------------------------------
-- Interpretations
-------------------------------------------------------------------------------

data Symbol =
    TypeSymbol Name
  | ConstSymbol Name
  deriving (Eq,Ord,Show)

data Interpret = Interpret Symbol Name
  deriving (Eq,Ord,Show)

data Interpretation = Interpretation (Map Symbol Name)

symbolName :: Symbol -> Name
symbolName (TypeSymbol n) = n
symbolName (ConstSymbol n) = n

destInterpret :: Interpret -> (Symbol,Name)
destInterpret (Interpret s n) = (s,n)

mkInterpretation :: Map Symbol Name -> Interpretation
mkInterpretation m = Interpretation (Map.filterWithKey norm m)
  where
    norm s n = symbolName s /= n

emptyInterpretation :: Interpretation
emptyInterpretation = mkInterpretation Map.empty

fromListInterpretation :: [Interpret] -> Maybe Interpretation
fromListInterpretation l = do
    guard (Map.size m == length l)
    return (mkInterpretation m)
  where
    m = Map.fromList $ map destInterpret l

fromListInterpretationUnsafe :: [Interpret] -> Interpretation
fromListInterpretationUnsafe l =
    case fromListInterpretation l of
      Just i -> i
      Nothing -> error "HOL.OpenTheory.fromListInterpretation failed"

instance Printable Symbol where
  toDoc (TypeSymbol n) = PP.text "type" <+> quoteName n
  toDoc (ConstSymbol n) = PP.text "const" <+> quoteName n

instance Parsable Symbol where
  parser = do
      k <- kind
      space
      n <- parser
      return $ k n
    where
      kind = (Parsec.string "type" >> return TypeSymbol)
             <|> (Parsec.string "const" >> return ConstSymbol)

      space = Parsec.skipMany1 spaceParser

instance Printable Interpret where
  toDoc (Interpret s n) = toDoc s <+> PP.text "as" <+> quoteName n

instance Parsable Interpret where
  parser = do
      s <- parser
      space
      _ <- Parsec.string "as"
      space
      n2 <- parser
      return $ Interpret s n2
    where
      space = Parsec.skipMany1 spaceParser

instance Printable Interpretation where
  toDoc (Interpretation m) = PP.vcat (map mk (Map.toList m))
    where
      mk (s,n) = toDoc (Interpret s n)

instance Parsable Interpretation where
  parser = do
      Parsec.skipMany eolParser
      ls <- Parsec.sepEndBy line (Parsec.skipMany1 eolParser)
      return $ fromListInterpretationUnsafe (mapMaybe id ls)
    where
      line = comment <|> interpretSymbol

      comment = do
        _ <- Parsec.char '#'
        Parsec.skipMany lineParser
        return Nothing

      interpretSymbol = do
        i <- parser
        Parsec.skipMany spaceParser
        return $ Just i

-------------------------------------------------------------------------------
-- Objects
-------------------------------------------------------------------------------

data Object =
    NumberObject Number
  | NameObject Name
  | ListObject [Object]
  | TypeOpObject TypeOp
  | TypeObject Type
  | ConstObject Const
  | VarObject Var
  | TermObject Term
  | ThmObject Thm
  deriving (Eq,Ord,Show)

class Objective a where
  toObject :: a -> Object

  fromObject :: Object -> Maybe a

instance Objective Object where
  toObject = id

  fromObject = Just

instance Objective Number where
  toObject = NumberObject

  fromObject (NumberObject i) = Just i
  fromObject _ = Nothing

instance Objective Name where
  toObject = NameObject

  fromObject (NameObject n) = Just n
  fromObject _ = Nothing

instance Objective a => Objective [a] where
  toObject = ListObject . map toObject

  fromObject (ListObject l) = mapM fromObject l
  fromObject _ = Nothing

instance Objective TypeOp where
  toObject = TypeOpObject

  fromObject (TypeOpObject t) = Just t
  fromObject _ = Nothing

instance Objective Type where
  toObject = TypeObject

  fromObject (TypeObject ty) = Just ty
  fromObject _ = Nothing

instance Objective Const where
  toObject = ConstObject

  fromObject (ConstObject c) = Just c
  fromObject _ = Nothing

instance Objective Var where
  toObject = VarObject

  fromObject (VarObject v) = Just v
  fromObject _ = Nothing

instance Objective Term where
  toObject = TermObject

  fromObject (TermObject tm) = Just tm
  fromObject _ = Nothing

instance Objective Thm where
  toObject = ThmObject

  fromObject (ThmObject th) = Just th
  fromObject _ = Nothing

instance (Objective a, Objective b) => Objective (a,b) where
  toObject (a,b) = ListObject [toObject a, toObject b]

  fromObject (ListObject [x,y]) = do
    a <- fromObject x
    b <- fromObject y
    return (a,b)
  fromObject _ = Nothing

sequentObject :: Object -> Object -> Maybe Sequent
sequentObject h c = do
  h' <- fromObject h
  c' <- fromObject c
  Sequent.mk (Set.fromList $ map TermAlpha.mk h') (TermAlpha.mk c')

pushObject :: Objective a => a -> [Object] -> [Object]
pushObject a s = toObject a : s

push2Object :: (Objective a, Objective b) => a -> b -> [Object] -> [Object]
push2Object a b s = pushObject a $ pushObject b s

push3Object :: (Objective a, Objective b, Objective c) =>
               a -> b -> c -> [Object] -> [Object]
push3Object a b c s = pushObject a $ push2Object b c s

push4Object :: (Objective a, Objective b, Objective c, Objective d) =>
               a -> b -> c -> d -> [Object] -> [Object]
push4Object a b c d s = pushObject a $ push3Object b c d s

push5Object :: (Objective a, Objective b, Objective c, Objective d,
                Objective e) => a -> b -> c -> d -> e -> [Object] -> [Object]
push5Object a b c d e s = pushObject a $ push4Object b c d e s

popObject :: Objective a => [Object] -> Maybe (a,[Object])
popObject [] = Nothing
popObject (x : xs) = fmap (\a -> (a,xs)) (fromObject x)

pop2Object :: (Objective a, Objective b) => [Object] -> Maybe (a,b,[Object])
pop2Object s = do
  (a,s') <- popObject s
  (b,s'') <- popObject s'
  return (a,b,s'')

pop3Object :: (Objective a, Objective b, Objective c) =>
              [Object] -> Maybe (a,b,c,[Object])
pop3Object s = do
  (a,s') <- popObject s
  (b,c,s'') <- pop2Object s'
  return (a,b,c,s'')

pop4Object :: (Objective a, Objective b, Objective c, Objective d) =>
              [Object] -> Maybe (a,b,c,d,[Object])
pop4Object s = do
  (a,s') <- popObject s
  (b,c,d,s'') <- pop3Object s'
  return (a,b,c,d,s'')

pop5Object :: (Objective a, Objective b, Objective c, Objective d,
               Objective e) => [Object] -> Maybe (a,b,c,d,e,[Object])
pop5Object s = do
  (a,s') <- popObject s
  (b,c,d,e,s'') <- pop4Object s'
  return (a,b,c,d,e,s'')

instance Printable Object where
  toDoc (NumberObject i) = toDoc i
  toDoc (NameObject n) = toDoc n
  toDoc (ListObject l) = toDoc l
  toDoc (TypeOpObject t) = toDoc t
  toDoc (TypeObject ty) = toDoc ty
  toDoc (ConstObject c) = toDoc c
  toDoc (VarObject v) = toDoc v
  toDoc (TermObject tm) = toDoc tm
  toDoc (ThmObject th) = toDoc th

-------------------------------------------------------------------------------
-- Commands
-------------------------------------------------------------------------------

data Command =
  -- Special commands
    NumberCommand Number
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

instance Parsable Command where
  parser = error "Parsec Command parser not implemented"

  fromText = regular
    where
      regular t =
         case Map.lookup t regulars of
           Just c -> Just c
           Nothing -> special t

      special t =
         case fromText t of
           Just n -> Just $ NameCommand n
           Nothing -> fmap NumberCommand $ fromText t

      regulars = Map.fromList $ map mk regularCommands
        where
          mk (c,s) = (Text.pack s, c)

instance Printable Command where
  toDoc =
      go
    where
      regulars = Map.fromList $ map (\(c,s) -> (c, PP.text s)) regularCommands

      go (NumberCommand i) = toDoc i
      go (NameCommand n) = toDoc n
      go DefineTypeOpLegacyCommand = legacy DefineTypeOpCommand
      go c = case Map.lookup c regulars of
               Just d -> d
               Nothing -> error $ "Unprintable command: " ++ show c

      legacy c = go c <+> PP.text "(legacy)"

-------------------------------------------------------------------------------
-- OpenTheory article file versions
-------------------------------------------------------------------------------

type Version = Number

supportedCommand :: Version -> Command -> Bool
supportedCommand (Number 5) DefineConstListCommand = False
supportedCommand (Number 5) DefineTypeOpCommand = False
supportedCommand (Number 5) HdTlCommand = False
supportedCommand (Number 5) PragmaCommand = False
supportedCommand (Number 5) ProveHypCommand = False
supportedCommand (Number 5) SymCommand = False
supportedCommand (Number 5) TransCommand = False
supportedCommand (Number 5) VersionCommand = False
supportedCommand (Number 6) DefineTypeOpLegacyCommand = False
supportedCommand _ _ = True

versionCommand :: Version -> Command -> Maybe Command
versionCommand (Number 5) DefineTypeOpCommand = Just DefineTypeOpLegacyCommand
versionCommand _ VersionCommand = Nothing
versionCommand v c = if supportedCommand v c then Just c else Nothing

-------------------------------------------------------------------------------
-- Execution state
-------------------------------------------------------------------------------

data State =
    State
      {stack :: [Object],
       dict :: Map Number Object,
       theorems :: Set Thm}
  deriving (Eq,Ord,Show)

pushState :: Objective a => a -> State -> State
pushState a state = state {stack = pushObject a $ stack state}

push2State :: (Objective a, Objective b) => a -> b -> State -> State
push2State a b state = state {stack = push2Object a b $ stack state}

push5State :: (Objective a, Objective b, Objective c, Objective d,
               Objective e) => a -> b -> c -> d -> e -> State -> State
push5State a b c d e state =
    state {stack = push5Object a b c d e $ stack state}

popState :: Objective a => State -> Maybe (a,State)
popState state = do
  (a,s) <- popObject $ stack state
  return (a, state {stack = s})

pop2State :: (Objective a, Objective b) => State -> Maybe (a,b,State)
pop2State state = do
  (a,b,s) <- pop2Object $ stack state
  return (a, b, state {stack = s})

pop3State :: (Objective a, Objective b, Objective c) =>
             State -> Maybe (a,b,c,State)
pop3State state = do
  (a,b,c,s) <- pop3Object $ stack state
  return (a, b, c, state {stack = s})

pop5State :: (Objective a, Objective b, Objective c, Objective d,
              Objective e) => State -> Maybe (a,b,c,d,e,State)
pop5State state = do
  (a,b,c,d,e,s) <- pop5Object $ stack state
  return (a, b, c, d, e, state {stack = s})

peekState :: Objective a => State -> Maybe a
peekState = fmap fst . popState

defState :: Number -> Object -> State -> State
defState k x state = state {dict = Map.insert k x $ dict state}

refState :: Number -> State -> Maybe Object
refState k state = Map.lookup k $ dict state

removeState :: Number -> State -> Maybe (Object,State)
removeState k state = do
  let d = dict state
  x <- Map.lookup k d
  let s = state {dict = Map.delete k d}
  return (x,s)

thmState :: Thm -> State -> State
thmState th state = state {theorems = Set.insert th $ theorems state}

initialState :: State
initialState =
    State
      {stack = [],
       dict = Map.empty,
       theorems = Set.empty}

executeCommand :: Theory -> State -> Command -> Maybe State
executeCommand thy state cmd =
    case cmd of
      NumberCommand i -> Just $ pushState i state
      NameCommand n -> Just $ pushState n state
      AbsTermCommand -> do
        (b,v,s) <- pop2State state
        let tm = Term.mkAbs v b
        return $ pushState tm s
      AbsThmCommand -> do
        (b,v,s) <- pop2State state
        th <- Thm.mkAbs v b
        return $ pushState th s
      AppTermCommand -> do
        (x,f,s) <- pop2State state
        tm <- Term.mkApp f x
        return $ pushState tm s
      AppThmCommand -> do
        (x,f,s) <- pop2State state
        th <- Thm.mkApp f x
        return $ pushState th s
      AssumeCommand -> do
        (tm,s) <- popState state
        th <- Thm.assume tm
        return $ pushState th s
      AxiomCommand -> do
        (c,h,s) <- pop2State state
        sq <- sequentObject h c
        th <- Theory.lookupThm thy sq
        return $ pushState th s
      BetaConvCommand -> do
        (tm,s) <- popState state
        th <- Thm.betaConv tm
        return $ pushState th s
      ConsCommand -> do
        (t,h,s) <- pop2State state
        return $ pushState ((h :: Object) : t) s
      ConstCommand -> do
        (n,s) <- popState state
        c <- Theory.lookupConst thy n
        return $ pushState c s
      ConstTermCommand -> do
        (ty,c,s) <- pop2State state
        let tm = Term.mkConst c ty
        return $ pushState tm s
      DeductAntisymCommand -> do
        (th1,th0,s) <- pop2State state
        let th = Thm.deductAntisym th0 th1
        return $ pushState th s
      DefCommand -> do
        (k,state') <- popState state
        x <- peekState state'
        return $ defState k x state'
      DefineConstCommand -> do
        (tm,n,s) <- pop2State state
        (c,th) <- Thm.defineConst n tm
        return $ push2State th c s
      DefineConstListCommand -> do
        (th,nvs,s) <- pop2State state
        (cs,def) <- Rule.defineConstList nvs th
        return $ push2State def cs s
      DefineTypeOpCommand -> do
        (th,tvn,rn,an,tn,s) <- pop5State state
        let tv = map TypeVar.mk tvn
        (t,a,r,ar,ra) <- Thm.defineTypeOp tn an rn tv th
        return $ push5State ra ar r a t s
      DefineTypeOpLegacyCommand -> do
        (th,tvn,rn,an,tn,s) <- pop5State state
        let tv = map TypeVar.mk tvn
        (t,a,r,ar,ra) <- Rule.defineTypeOpLegacy tn an rn tv th
        return $ push5State ra ar r a t s
      EqMpCommand -> do
        (th1,th0,s) <- pop2State state
        th <- Thm.eqMp th0 th1
        return $ pushState th s
      HdTlCommand -> do
        (l,s) <- popState state
        (h,t) <- case l of
                   [] -> Nothing
                   x : xs -> Just (x,xs)
        return $ push2State t (h :: Object) s
      NilCommand -> Just $ pushState ([] :: [Object]) state
      OpTypeCommand -> do
        (tys,t,s) <- pop2State state
        let ty = Type.mkOp t tys
        return $ pushState ty s
      PopCommand -> do
        (_,s) <- (popState :: State -> Maybe (Object,State)) state
        return s
      PragmaCommand -> do
        (_,s) <- (popState :: State -> Maybe (Object,State)) state
        return s
      ProveHypCommand -> do
        (th1,th0,s) <- pop2State state
        th <- Rule.proveHyp th0 th1
        return $ pushState th s
      RefCommand -> do
        (k,s) <- popState state
        x <- refState k s
        return $ pushState x s
      ReflCommand -> do
        (tm,s) <- popState state
        let th = Thm.refl tm
        return $ pushState th s
      RemoveCommand -> do
        (k,s) <- popState state
        (x,s') <- removeState k s
        return $ pushState x s'
      SubstCommand -> do
        (th,(nty,vtm),s) <- pop2State state
        let vty = map (\(n,ty) -> (TypeVar.mk n, ty)) nty
        sub <- Subst.fromList vty vtm
        let th' = Thm.subst sub th
        return $ pushState th' s
      SymCommand -> do
        (th,s) <- popState state
        th' <- Rule.sym th
        return $ pushState th' s
      ThmCommand -> do
        (c,h,th,s) <- pop3State state
        sq <- sequentObject h c
        th' <- Rule.alphaSequent sq th
        return $ thmState th' s
      TransCommand -> do
        (th1,th0,s) <- pop2State state
        th <- Rule.trans th0 th1
        return $ pushState th s
      TypeOpCommand -> do
        (n,s) <- popState state
        t <- Theory.lookupTypeOp thy n
        return $ pushState t s
      VarCommand -> do
        (ty,n,s) <- pop2State state
        let v = Var.mk n ty
        return $ pushState v s
      VarTermCommand -> do
        (v,s) <- popState state
        let tm = Term.mkVar v
        return $ pushState tm s
      VarTypeCommand -> do
        (n,s) <- popState state
        let ty = Type.mkVar $ TypeVar.mk n
        return $ pushState ty s
      _ -> Nothing

instance Printable State where
  toDoc state =
      stackDoc (stack state) $+$
      dictDoc (dict state) $+$
      theoremsDoc (theorems state)
    where
      stackDoc s = PP.text "stack =" <+> (PP.brackets $ objsDoc 5 s)

      dictDoc d = PP.text "dictionary =" <+> (PP.braces $ PP.int $ Map.size d)

      theoremsDoc e = PP.text "theorems =" <+> (PP.braces $ PP.int $ Set.size e)

      objsDoc k s =
          PP.sep $ PP.punctuate PP.comma ds
        where
          ds = if x <= 1 then map toDoc s
               else map toDoc (take k s) ++ [dx]
          dx = dots <> PP.int x <+> PP.text "more objects" <> dots
          dots = PP.text "..."
          x = length s - k

-------------------------------------------------------------------------------
-- Reading an OpenTheory article file
-------------------------------------------------------------------------------

type LineNumber = Integer

readArticle :: Theory -> FilePath -> IO (Set Thm)
readArticle thy art = do
    bs <- ByteString.readFile art
    let txt = Text.Encoding.decodeUtf8 bs
    let ls = zip [1..] $ Text.lines txt
    let (v,cs) = getVersion $ map parseCmd $ filter notComment ls
    let s = List.foldl' execute initialState $ map (version v) cs
    return $ theorems s
  where
    notComment :: (LineNumber,Text) -> Bool
    notComment (_,t) = Text.null t || Text.head t /= '#'

    parseCmd :: (LineNumber,Text) -> (LineNumber,Command)
    parseCmd (l,t) =
        case fromText t of
          Just c -> (l,c)
          Nothing -> error $ err "unparseable command" l (show t)

    getVersion :: [(LineNumber,Command)] -> (Version,[(LineNumber,Command)])
    getVersion ((l, NumberCommand v) : (_,VersionCommand) : cs) =
        if v == Number 6 then (v,cs)
        else error $ err "bad version number" l (show v)
    getVersion cs = (Number 5, cs)

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
          Nothing -> error $ err e l (toString s)
                     where e = "couldn't execute command " ++ toString c

    err :: String -> LineNumber -> String -> String
    err e l s = art ++ ":" ++ show l ++ ": " ++ e ++ ":\n" ++ s

-------------------------------------------------------------------------------
-- Theory names
-------------------------------------------------------------------------------

newtype TheoryName = TheoryName {destTheoryName :: String}
  deriving (Eq,Ord,Show)

instance Printable TheoryName where
  toDoc = PP.text . destTheoryName

instance Parsable TheoryName where
  parser = do
      cs <- Parsec.sepBy1 component (Parsec.char sep)
      return $ TheoryName (List.intercalate [sep] cs)
    where
      component = do
          h <- Parsec.lower
          t <- Parsec.many (Parsec.lower <|> Parsec.digit)
          return (h : t)

      sep = '-'

-------------------------------------------------------------------------------
-- Theory values
-------------------------------------------------------------------------------

data TheoryValue = TheoryValue TheoryName String
  deriving (Eq,Ord,Show)

instance Printable TheoryValue where
  toDoc (TheoryValue k v) = toDoc k <> PP.char ':' <+> PP.text v

instance Parsable TheoryValue where
  parser = do
      Parsec.skipMany spaceParser
      n <- parser
      Parsec.skipMany spaceParser
      _ <- Parsec.char ':'
      Parsec.skipMany spaceParser
      v <- Parsec.many lineParser
      return $ TheoryValue n (List.dropWhileEnd Char.isSpace v)

printTheoryValue :: Printable a => TheoryName -> a -> TheoryValue
printTheoryValue n a = TheoryValue n (toString a)

matchTheoryValue :: TheoryName -> TheoryValue -> Maybe String
matchTheoryValue n (TheoryValue k v) = if k == n then Just v else Nothing

parseTheoryValue :: Parsable a => TheoryName -> TheoryValue -> Maybe a
parseTheoryValue n v = do
    s <- matchTheoryValue n v
    a <- fromString s
    return a

-------------------------------------------------------------------------------
-- Theory information
-------------------------------------------------------------------------------

newtype TheoryInfo = TheoryInfo {destTheoryInfo :: [TheoryValue]}
  deriving (Eq,Ord,Show)

nullTheoryInfo :: TheoryInfo -> Bool
nullTheoryInfo = null . destTheoryInfo

appendTheoryInfo :: TheoryInfo -> TheoryInfo -> TheoryInfo
appendTheoryInfo (TheoryInfo l) (TheoryInfo l') = TheoryInfo (l ++ l')

concatTheoryInfo :: [TheoryInfo] -> TheoryInfo
concatTheoryInfo = TheoryInfo . concat . map destTheoryInfo

firstTheoryInfo :: (TheoryValue -> Maybe a) ->
                   TheoryInfo -> Maybe (a,TheoryInfo)
firstTheoryInfo f = g [] . destTheoryInfo
  where
    g _ [] = Nothing
    g l (h : t) = case f h of
                    Just a -> Just (a, TheoryInfo (foldl (flip (:)) t l))
                    Nothing -> g (h : l) t

getFirstTheoryInfo :: [TheoryInfo -> Maybe (a,TheoryInfo)] ->
                      TheoryInfo -> Maybe (a,TheoryInfo)
getFirstTheoryInfo [] _ = Nothing
getFirstTheoryInfo (f : fs) i =
    case f i of
      Nothing -> getFirstTheoryInfo fs i
      x -> x

getMapTheoryInfo :: (a -> b) -> (TheoryInfo -> Maybe (a,TheoryInfo)) ->
                    TheoryInfo -> Maybe (b,TheoryInfo)
getMapTheoryInfo f g = let f0 (a,i) = (f a, i) in fmap f0 . g

getMaybeTheoryInfo :: (TheoryInfo -> Maybe (a,TheoryInfo)) ->
                      TheoryInfo -> Maybe (Maybe a, TheoryInfo)
getMaybeTheoryInfo f i =
    case f i of
      Just (a,i') -> Just (Just a, i')
      Nothing -> Just (Nothing,i)

instance Printable TheoryInfo where
  toDoc = PP.vcat . map toDoc . destTheoryInfo

instance Parsable TheoryInfo where
  parser = fmap TheoryInfo $ Parsec.endBy parser eolParser

class Informative a where
  toInfo :: a -> TheoryInfo

  getInfo :: TheoryInfo -> Maybe (a,TheoryInfo)

  fromInfo :: TheoryInfo -> Maybe a
  fromInfo i = do
      (a,i') <- getInfo i
      guard $ nullTheoryInfo i'
      return a

instance Informative a => Informative [a] where
  toInfo = concatTheoryInfo . map toInfo

  getInfo = g []
    where
      g l i = case getInfo i of
                Just (a,i') -> g (a : l) i'
                Nothing -> Just (l,i)

instance (Informative a, Informative b) => Informative (a,b) where
  toInfo (a,b) = appendTheoryInfo (toInfo a) (toInfo b)

  getInfo i = do
      (a,i') <- getInfo i
      (b,i'') <- getInfo i'
      return ((a,b),i'')

-------------------------------------------------------------------------------
-- Theory file paths
-------------------------------------------------------------------------------

newtype TheoryFilePath = TheoryFilePath {destTheoryFilePath :: FilePath}
  deriving (Eq,Ord,Show)

instance Printable TheoryFilePath where
  toDoc = PP.doubleQuotes . PP.text . destTheoryFilePath

instance Parsable TheoryFilePath where
  parser = do
      _ <- Parsec.char '"'
      f <- Parsec.many (Parsec.noneOf "\"\n")
      _ <- Parsec.char '"'
      return $ TheoryFilePath f

-------------------------------------------------------------------------------
-- Theory interpretations
-------------------------------------------------------------------------------

data TheoryInterpret =
    TheoryInterpret Interpret
  | TheoryInterpretation TheoryFilePath
  deriving (Eq,Ord,Show)

instance Informative TheoryInterpret where
  toInfo (TheoryInterpret i) =
      TheoryInfo [printTheoryValue (TheoryName "interpret") i]
  toInfo (TheoryInterpretation f) =
      TheoryInfo [printTheoryValue (TheoryName "interpretation") f]

  getInfo =
      getFirstTheoryInfo [getInterpret,getInterpretation]
    where
      getInterpret =
        getMapTheoryInfo TheoryInterpret
          (firstTheoryInfo (parseTheoryValue (TheoryName "interpret")))

      getInterpretation =
        getMapTheoryInfo TheoryInterpretation
          (firstTheoryInfo (parseTheoryValue (TheoryName "interpretation")))

-------------------------------------------------------------------------------
-- Theory blocks
-------------------------------------------------------------------------------

newtype TheoryBlockName = TheoryBlockName {destTheoryBlockName :: TheoryName}
  deriving (Eq,Ord,Show)

data TheoryBlockOperation =
    ArticleBlock TheoryFilePath
  | PackageBlock {package :: String, checksum :: Maybe String}
  | UnionBlock
  deriving (Eq,Ord,Show)

data TheoryBlock =
    TheoryBlock
      {name :: TheoryBlockName,
       imports :: [TheoryBlockName],
       interpret :: [TheoryInterpret],
       operation :: TheoryBlockOperation}
  deriving (Eq,Ord,Show)

instance Printable TheoryBlockName where
  toDoc = toDoc . destTheoryBlockName

instance Parsable TheoryBlockName where
  parser = fmap TheoryBlockName parser

instance Informative TheoryBlockName where
  toInfo n = TheoryInfo [printTheoryValue (TheoryName "import") n]

  getInfo = firstTheoryInfo (parseTheoryValue (TheoryName "import"))

instance Informative TheoryBlockOperation where
  toInfo (ArticleBlock f) = TheoryInfo [fv]
    where
      fv = printTheoryValue (TheoryName "article") f
  toInfo (PackageBlock p c) = TheoryInfo (pv : cv)
    where
      pv = TheoryValue (TheoryName "package") p
      cv = case c of
             Just s -> [TheoryValue (TheoryName "checksum") s]
             Nothing -> []
  toInfo UnionBlock = TheoryInfo []

  getInfo =
      getFirstTheoryInfo [getArticleBlock,getPackageBlock,getUnionBlock]
    where
      getArticleBlock = getMapTheoryInfo ArticleBlock getArticle

      getPackageBlock i = do
        (p,i') <- getPackage i
        (c,i'') <- getMaybeTheoryInfo getChecksum i'
        return (PackageBlock p c, i'')

      getUnionBlock i = Just (UnionBlock,i)

      getArticle = firstTheoryInfo (parseTheoryValue (TheoryName "article"))
      getPackage = firstTheoryInfo (matchTheoryValue (TheoryName "package"))
      getChecksum = firstTheoryInfo (matchTheoryValue (TheoryName "checksum"))

mkTheoryBlock :: TheoryBlockName -> TheoryInfo -> Maybe TheoryBlock
mkTheoryBlock n info = do
    (imp,(int,op)) <- fromInfo info
    guard (op /= UnionBlock || null int)
    return $ TheoryBlock n imp int op

destTheoryBlock :: TheoryBlock -> (TheoryBlockName,TheoryInfo)
destTheoryBlock (TheoryBlock n imp int op) = (n, toInfo (imp,(int,op)))

instance Printable TheoryBlock where
  toDoc b =
      (toDoc n <+> PP.lbrace) $+$
      PP.nest 2 (toDoc i) $+$
      PP.rbrace
    where
      (n,i) = destTheoryBlock b

instance Parsable TheoryBlock where
  parser = do
      n <- opener
      i <- parser
      closer
      case mkTheoryBlock n i of
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
-- Theory files
-------------------------------------------------------------------------------

data TheoryFile = TheoryFile TheoryInfo [TheoryBlock]
  deriving (Eq,Ord,Show)

instance Printable TheoryFile where
  toDoc (TheoryFile i bs) =
      PP.vcat (List.intersperse (PP.text "") (toDoc i : map toDoc bs))

instance Parsable TheoryFile where
  parser = do
      Parsec.skipMany eolParser
      i <- parser
      Parsec.skipMany eolParser
      bs <- Parsec.sepEndBy parser (Parsec.skipMany1 eolParser)
      return $ TheoryFile i bs

-------------------------------------------------------------------------------
-- Interface to the opentheory tool
-------------------------------------------------------------------------------

opentheory :: [String] -> IO String
opentheory args = System.Process.readProcess "opentheory" args []
