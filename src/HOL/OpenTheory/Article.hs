{- |
module: $Header$
description: OpenTheory article files
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.OpenTheory.Article
where

import qualified Data.ByteString.Lazy as ByteString
import qualified Data.List as List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.Encoding as Text.Encoding
import Prelude hiding ((<>))
import Text.Parsec.Text.Lazy ()
import Text.PrettyPrint ((<>),(<+>),($+$))
import qualified Text.PrettyPrint as PP

import HOL.Data
import HOL.Name
import HOL.OpenTheory.Interpret (Interpret,interpretConst,interpretTypeOp)
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

executeCommand :: Theory -> Interpret -> State -> Command -> Maybe State
executeCommand thy int state cmd =
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
        let n' = interpretConst int n
        c <- Theory.lookupConst thy n'
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
        let n' = interpretConst int n
        (c,th) <- Thm.defineConst n' tm
        return $ push2State th c s
      DefineConstListCommand -> do
        (th,nvs,s) <- pop2State state
        let nvs' = map (\(n,v) -> (interpretConst int n, v)) nvs
        (cs,def) <- Rule.defineConstList nvs' th
        return $ push2State def cs s
      DefineTypeOpCommand -> do
        (th,tv,rn,an,tn,s) <- pop5State state
        let tn' = interpretTypeOp int tn
        let an' = interpretConst int an
        let rn' = interpretConst int rn
        let tv' = map TypeVar.mk tv
        (t,a,r,ar,ra) <- Thm.defineTypeOp tn' an' rn' tv' th
        return $ push5State ra ar r a t s
      DefineTypeOpLegacyCommand -> do
        (th,tv,rn,an,tn,s) <- pop5State state
        let tn' = interpretTypeOp int tn
        let an' = interpretConst int an
        let rn' = interpretConst int rn
        let tv' = map TypeVar.mk tv
        (t,a,r,ar,ra) <- Rule.defineTypeOpLegacy tn' an' rn' tv' th
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
        let n' = interpretTypeOp int n
        t <- Theory.lookupTypeOp thy n'
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

readArticle :: Theory -> Interpret -> FilePath -> IO (Set Thm)
readArticle thy int art = do
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
        case executeCommand thy int s c of
          Just s' -> s'
          Nothing -> error $ err e l (toString s)
                     where e = "couldn't execute command " ++ toString c

    err :: String -> LineNumber -> String -> String
    err e l s = art ++ ":" ++ show l ++ ": " ++ e ++ ":\n" ++ s
