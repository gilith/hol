{- |
module: $Header$
description: Pretty-printing
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.Print
where

import Control.Monad (guard)
import qualified Data.Char as Char
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (isJust)
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint ((<>),(<+>))
import qualified Text.PrettyPrint as PP

import qualified HOL.Const as Const
import HOL.Data
import HOL.Name
import HOL.Sequent (Sequent)
import qualified HOL.Sequent as Sequent
import qualified HOL.Term as Term
import HOL.TermAlpha (TermAlpha)
import qualified HOL.TermAlpha as TermAlpha
import HOL.Thm (Thm)
import qualified HOL.Thm as Thm
import qualified HOL.Type as Type
import qualified HOL.TypeOp as TypeOp
import qualified HOL.TypeVar as TypeVar
import qualified HOL.Var as Var

-------------------------------------------------------------------------------
-- Printing prefix operators
-------------------------------------------------------------------------------

type PrefixOp = PP.Doc -> PP.Doc

ppPrefixOps :: [PrefixOp] -> PP.Doc -> PP.Doc
ppPrefixOps = flip $ foldr (\p d -> p d)

-------------------------------------------------------------------------------
-- Printing infix operators
-------------------------------------------------------------------------------

type Prec = Int

data Assoc =
    LeftAssoc
  | RightAssoc
  | NonAssoc
  deriving (Eq,Ord,Show)

type InfixOp = (Prec, Assoc, PP.Doc -> PP.Doc)

ppInfixOps :: (a -> Maybe (InfixOp,a,a)) -> (Bool -> a -> PP.Doc) -> a -> PP.Doc
ppInfixOps dest pp =
    go Nothing True
  where
    go mprec rightmost a =
        case dest a of
          Nothing -> base
          Just ((prec,assoc,op),x,y) ->
              if not (tightEnough prec mprec) then base
              else PP.fsep $ goList prec assoc rightmost x y op
      where
        base = pp rightmost a

    goList prec LeftAssoc rightmost x y op =
        goLeft prec x op [goNext prec rightmost y]
    goList prec RightAssoc rightmost x y op =
        op (goNext prec False x) : goRight prec rightmost y
    goList prec NonAssoc rightmost x y op =
        [op (goNext prec False x), goNext prec rightmost y]

    goLeft prec a rop ds =
        case dest a of
          Nothing -> base
          Just ((prec',assoc,op),x,y) ->
              if prec' /= prec then base
              else if assoc /= LeftAssoc then error "mixed associativity"
              else goLeft prec x op (rop (goNext prec False y) : ds)
      where
        base = rop (goNext prec False a) : ds

    goRight prec rightmost a =
        case dest a of
          Nothing -> base
          Just ((prec',assoc,op),x,y) ->
              if prec' /= prec then base
              else if assoc /= RightAssoc then error "mixed associativity"
              else op (goNext prec False x) : goRight prec rightmost y
      where
        base = [goNext prec rightmost a]

    goNext prec rightmost a = go (Just (prec + 1)) rightmost a

    tightEnough _ Nothing = True
    tightEnough prec (Just mprec) = mprec <= prec

-------------------------------------------------------------------------------
-- Printable types
-------------------------------------------------------------------------------

class Printable a where
  toDoc :: a -> PP.Doc

  toString :: a -> String
  toString =
      PP.renderStyle style . toDoc
    where
      style = PP.style {PP.lineLength = 80}

instance Printable Integer where
  toDoc = PP.integer

instance Printable a => Printable [a] where
  toDoc = PP.brackets . PP.fsep . PP.punctuate PP.comma . map toDoc

instance Printable a => Printable (Set a) where
  toDoc = PP.braces . PP.sep . PP.punctuate PP.comma . map toDoc . Set.toList

-------------------------------------------------------------------------------
-- Names
-------------------------------------------------------------------------------

instance Printable Namespace where
  toDoc =
      go
    where
      go (Namespace []) = pr0
      go (Namespace l) = pr1 l

      pr0 = PP.text "<empty>"
      pr1 = PP.hcat . PP.punctuate (PP.text ".") . map PP.text

instance Printable Name where
  toDoc (Name (Namespace l) s) = toDoc (Namespace (l ++ [s]))

-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

instance Printable TypeVar where
  toDoc = toDoc . TypeVar.dest

instance Printable TypeOp where
  toDoc = toDoc . TypeOp.name

instance Printable Type where
  toDoc =
      normal
    where
      basic _ ty =
          if isInfix ty then parens ty
          else case Type.dest ty of
                 VarType v -> toDoc v
                 OpType t [] -> toDoc t
                 OpType t [x] -> basic False x <+> toDoc t
                 OpType t xs -> normals xs <+> toDoc t

      normal = ppInfixOps destInfix basic

      normals = PP.parens . PP.fsep . PP.punctuate (PP.text ",") . map normal

      parens = PP.parens . normal

      -------------------------------------------------------------------------
      -- These grammar tables control type printing
      -------------------------------------------------------------------------

      infixTable =
          [--
           -- Primitives
           (TypeOp.funName, 4, RightAssoc, Nothing)]

      -------------------------------------------------------------------------
      -- Infix operators
      -------------------------------------------------------------------------

      mkInfixOp (n,p,a,x) =
          (n, (p, a, flip (<+>) $ PP.text s))
        where
          s = case x of
                Just y -> y
                Nothing -> let Name _ y = n in y

      infixOps :: Map Name InfixOp
      infixOps = Map.fromList $ map mkInfixOp infixTable

      destBinary ty =
          case Type.dest ty of
            OpType t [x,y] -> Just (t,x,y)
            _ -> Nothing

      destInfix :: Type -> Maybe (InfixOp,Type,Type)
      destInfix ty = do
          (t,x,y) <- destBinary ty
          i <- lookupOp (TypeOp.name t)
          return (i,x,y)
        where
          lookupOp n = Map.lookup n infixOps

      isInfix = isJust . destInfix

-------------------------------------------------------------------------------
-- Terms
-------------------------------------------------------------------------------

instance Printable Const where
  toDoc =
      parenSymbol . showName . Const.name
    where
      showName (Name ns s) = Name (showNamespace ns) s
      showNamespace (Namespace ns) = Namespace (List.dropWhile isUpper ns)
      isUpper [] = False
      isUpper (c : _) = Char.isUpper c

      parenSymbol n = (if symbolName n then PP.parens else id) $ toDoc n
      symbolName (Name (Namespace ns) s) = isSymbol (concat ns ++ s)
      isSymbol [] = False
      isSymbol (c : _) = not (Char.isAlphaNum c)

instance Printable Var where
  toDoc = toDoc . Var.name

instance Printable Term where
  toDoc =
      normal
    where
      basic tm =
          case destNumeral tm of
            Just i -> PP.integer i
            Nothing ->
              case Term.dest tm of
                VarTerm v -> toDoc v
                ConstTerm c _ -> toDoc c
                _ -> parens tm

      application tm =
          case stripGenApp tm of
            (_,[]) -> basic tm
            (f,xs) -> basic f <+> PP.sep (map basic xs)

      binder rightmost tm =
          case destBinder tm of
            Just (b,v,t) ->
                if rightmost then ppBinder b (map basic v) (normal t)
                else parens tm
            Nothing -> application tm

      negation rightmost tm =
          case stripNegation tm of
            ([],_) -> binder rightmost tm
            (ns,t) -> ppPrefixOps ns $ binder rightmost t

      letterm rightmost tm =
          case stripLet tm of
            ([],_) -> negation rightmost tm
            (ves,t) -> if not rightmost then parens tm
                       else ppLet application normal ves t

      conditional rightmost tm =
          case stripCond tm of
            ([],_) -> letterm rightmost tm
            ((c,t) : cts, e) -> if not rightmost then parens tm
                                else ppCond normal c t cts e

      normal = ppInfixOps destInfix conditional

      parens = PP.parens . normal

      -------------------------------------------------------------------------
      -- These grammar tables control term printing
      -------------------------------------------------------------------------

      infixTable =
          [--
           -- Booleans
           (Const.conjName, -1, RightAssoc, Nothing),
           (Const.disjName, -2, RightAssoc, Nothing),
           (Const.impName, -3, RightAssoc, Nothing),
           --
           -- Functions
           (Const.composeName, 4, LeftAssoc, Nothing),
           --
           -- Natural numbers
           (Const.powerName, 9, RightAssoc, Nothing),
           (Const.multName, 8, LeftAssoc, Nothing),
           (Const.divName, 7, LeftAssoc, Nothing),
           (Const.modName, 7, LeftAssoc, Nothing),
           (Const.addName, 6, LeftAssoc, Nothing),
           (Const.subName, 6, LeftAssoc, Nothing),
           (Const.leName, 3, NonAssoc, Nothing),
           (Const.ltName, 3, NonAssoc, Nothing),
           (Const.geName, 3, NonAssoc, Nothing),
           (Const.gtName, 3, NonAssoc, Nothing),
           --
           -- Set theory
           (Const.intersectName, 7, LeftAssoc, Nothing),
           (Const.differenceName, 6, LeftAssoc, Nothing),
           (Const.unionName, 6, LeftAssoc, Nothing),
           (Const.inName, 3, NonAssoc, Nothing),
           (Const.subsetName, 3, NonAssoc, Nothing),
           --
           --  List theory
           (Const.appendName, 5, RightAssoc, Nothing),
           (Const.consName, 5, RightAssoc, Nothing)]

      quantifierTable =
          [(Const.selectName, Nothing),
           (Const.forallName, Nothing),
           (Const.existsName, Nothing),
           (Const.existsUniqueName, Nothing)]

      negationTable =
          [(Const.negName, Nothing)]

      -------------------------------------------------------------------------
      -- Infix operators
      -------------------------------------------------------------------------

      mkInfixOp (n,p,a,x) =
          (n, (p, a, flip (<+>) $ PP.text s))
        where
          s = case x of
                Just y -> y
                Nothing -> let Name _ y = n in y

      eqInfixOp :: InfixOp
      eqInfixOp = snd $ mkInfixOp (Const.eqName, 3, NonAssoc, Nothing)

      iffInfixOp :: InfixOp
      iffInfixOp = snd $ mkInfixOp (Const.eqName, -4, NonAssoc, Just "<=>")

      infixOps :: Map Name InfixOp
      infixOps = Map.fromList $ map mkInfixOp infixTable

      destInfix :: Term -> Maybe (InfixOp,Term,Term)
      destInfix tm = do
          (cx,y) <- Term.destApp tm
          (c,x) <- Term.destApp cx
          n <- fmap (Const.name . fst) $ Term.destConst c
          i <- lookupOp n
          return (i,x,y)
        where
          lookupOp n =
              if n /= Const.eqName then Map.lookup n infixOps
              else if Term.isBool tm then Just iffInfixOp
              else Just eqInfixOp

      isInfix = isJust . destInfix

      -------------------------------------------------------------------------
      -- Prefix operators
      -------------------------------------------------------------------------

      mkPrefixOp (n,x) =
          (n, join $ PP.text s)
        where
          s = case x of
                Just y -> y
                Nothing -> let Name _ y = n in y

          join = case reverse s of
                   c : _ | Char.isAlphaNum c -> (<+>)
                   _ -> (<>)

      -------------------------------------------------------------------------
      -- Lambda abstractions
      -------------------------------------------------------------------------

      destAbs :: Term -> Maybe (Term,Term)
      destAbs tm = do
          (v,b) <- Term.destAbs tm
          return (Term.mkVar v, b)

      lambda :: PrefixOp
      lambda = snd $ mkPrefixOp (undefined, Just "\\")

      destLambda :: Term -> Maybe (PrefixOp,[Term],Term)
      destLambda tm = do
          (v,t) <- destAbs tm
          let (vs,b) = strip t
          return (lambda, v : vs, b)
        where
          strip t =
              case destAbs t of
                Just (v,u) -> (v : vs, b) where (vs,b) = strip u
                Nothing -> ([],t)

      -------------------------------------------------------------------------
      -- Quantifiers
      -------------------------------------------------------------------------

      quantifiers :: Map Name PrefixOp
      quantifiers = Map.fromList $ map mkPrefixOp quantifierTable

      destQuantifier :: Term -> Maybe (PrefixOp,[Term],Term)
      destQuantifier tm = do
          (c,v,t) <- dest tm
          q <- Map.lookup (Const.name c) quantifiers
          let (vs,b) = strip c t
          return (q, v : vs, b)
        where
          dest t = do
              (q,vb) <- Term.destApp t
              (c,_) <- Term.destConst q
              (v,b) <- destAbs vb
              return (c,v,b)

          strip c t =
              case dest t of
                Just (c',v,u) | c' == c -> (v : vs, b) where (vs,b) = strip c u
                _ -> ([],t)

      -------------------------------------------------------------------------
      -- Binders
      -------------------------------------------------------------------------

      destBinder :: Term -> Maybe (PrefixOp,[Term],Term)
      destBinder tm =
          case destQuantifier tm of
            Just b -> Just b
            Nothing -> destLambda tm

      isBinder = isJust . destBinder

      ppBinder :: PrefixOp -> [PP.Doc] -> PP.Doc -> PP.Doc
      ppBinder b v t = b $ PP.sep [PP.fsep v <> PP.text ".", t]

      -------------------------------------------------------------------------
      -- Negation operators
      -------------------------------------------------------------------------

      negations :: Map Name PrefixOp
      negations = Map.fromList $ map mkPrefixOp negationTable

      destNegation :: Term -> Maybe (PrefixOp,Term)
      destNegation tm = do
          (c,t) <- Term.destApp tm
          n <- fmap (Const.name . fst) $ Term.destConst c
          p <- Map.lookup n negations
          return (p,t)

      isNegation = isJust . destNegation

      stripNegation :: Term -> ([PrefixOp],Term)
      stripNegation tm =
          case destNegation tm of
            Just (n,t) -> (n : ns, b) where (ns,b) = stripNegation t
            Nothing -> ([],tm)

      -------------------------------------------------------------------------
      -- Conditionals
      -------------------------------------------------------------------------

      destCond :: Term -> Maybe (Term,Term,Term)
      destCond tm = do
          (ict,e) <- Term.destApp tm
          (ic,t) <- Term.destApp ict
          (i,c) <- Term.destApp ic
          (x,_) <- Term.destConst i
          guard (Const.name x == Const.condName)
          return (c,t,e)

      isCond = isJust . destCond

      stripCond :: Term -> ([(Term,Term)],Term)
      stripCond tm =
          case destCond tm of
            Just (c,t,u) -> ((c,t) : cts, e) where (cts,e) = stripCond u
            Nothing -> ([],tm)

      ppCond :: (Term -> PP.Doc) -> Term -> Term -> [(Term,Term)] -> Term ->
                PP.Doc
      ppCond pp =
          \c t cts e ->
            PP.sep (ifThen c t : map elseIfThen cts ++ [elseBranch e])
        where
          ifThen c t =
              PP.text "if" <+> PP.sep [pp c, PP.text "then" <+> pp t]

          elseIfThen (c,t) =
              PP.text "else" <+> PP.sep [PP.text "if" <+> pp c,
                                         PP.text "then" <+> pp t]

          elseBranch e = PP.text "else" <+> pp e

      -------------------------------------------------------------------------
      -- Lets
      -------------------------------------------------------------------------

      destLet :: Term -> Maybe (Term,Term,Term)
      destLet tm = do
          (vt,e) <- Term.destApp tm
          (v,t) <- destAbs vt
          return (v,e,t)

      isLet = isJust . destLet

      stripLet :: Term -> ([(Term,Term)],Term)
      stripLet tm =
          case destLet tm of
            Just (v,e,u) -> ((v,e) : ves, t) where (ves,t) = stripLet u
            Nothing -> ([],tm)

      ppLet :: (Term -> PP.Doc) -> (Term -> PP.Doc) ->
               [(Term,Term)] -> Term -> PP.Doc
      ppLet ppv pp =
          \ves t ->
            PP.sep (map letBind ves ++ [pp t])
        where
          letBind (v,e) =
              PP.text "let" <+> PP.sep [ppv v <+> PP.text "<-",
                                        pp e <+> PP.text "in"]

      -------------------------------------------------------------------------
      -- Numerals
      -------------------------------------------------------------------------

      isZero :: Term -> Bool
      isZero tm =
          case Term.destConst tm of
            Just (c,_) -> Const.name c == Const.zeroName
            Nothing -> False

      destBit :: Term -> Maybe (Bool,Term)
      destBit tm = do
          (b,t) <- Term.destApp tm
          (c,_) <- Term.destConst b
          fmap (flip (,) t) $ bit (Const.name c)
        where
          bit n = if n == Const.bit0Name then Just False
                  else if n == Const.bit1Name then Just True
                  else Nothing

      destNumeral :: Term -> Maybe Integer
      destNumeral tm =
          if isZero tm then Just 0
          else do
            (b,t) <- destBit tm
            i <- destNumeral t
            bit b i
        where
          bit False 0 = Nothing
          bit b i = Just (2 * i + (if b then 1 else 0))

      isNumeral = isJust . destNumeral

      -------------------------------------------------------------------------
      -- Function application
      -------------------------------------------------------------------------

      destGenApp :: Term -> Maybe (Term,Term)
      destGenApp tm = do
          guard (not $ isNumeral tm)
          guard (not $ isCond tm)
          --guard (not $ isPair tm)
          guard (not $ isLet tm)
          --guard (not $ isComprehension tm)
          guard (not $ isInfix tm)
          guard (not $ isNegation tm)
          guard (not $ isBinder tm)
          --guard (not $ isCase tm)
          Term.destApp tm

      stripGenApp :: Term -> (Term,[Term])
      stripGenApp =
          go []
        where
          go xs tm =
              case destGenApp tm of
                Nothing -> (tm,xs)
                Just (f,x) -> go (x : xs) f

instance Printable TermAlpha where
  toDoc = toDoc . TermAlpha.dest

-------------------------------------------------------------------------------
-- Theorems
-------------------------------------------------------------------------------

instance Printable Sequent where
  toDoc sq =
      PP.sep [hd, PP.text "|-" <+> toDoc c]
    where
      (h,c) = Sequent.dest sq
      hd = if Set.null h then PP.empty else toDoc h

instance Printable Thm where
  toDoc = toDoc . Thm.dest
