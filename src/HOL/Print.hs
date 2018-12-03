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
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
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
import HOL.TypeSubst (TypeSubst)
import qualified HOL.TypeSubst as TypeSubst
import qualified HOL.TypeVar as TypeVar
import qualified HOL.Var as Var

-------------------------------------------------------------------------------
-- Printing symbol names
-------------------------------------------------------------------------------

isSymbolChar :: Char -> Bool
isSymbolChar = not . Char.isAlphaNum

isSymbolString :: String -> Bool
isSymbolString [] = True
isSymbolString ['o'] = True
isSymbolString ['(',')'] = False
isSymbolString ['[',']'] = False
isSymbolString ['{','}'] = False
isSymbolString (c : _) = isSymbolChar c

ppSymbolName :: Name -> PP.Doc
ppSymbolName =
    parenSymbol . showName
  where
    showName (Name ns s) = Name (showNamespace ns) s
    showNamespace (Namespace ns) = Namespace (List.dropWhile isUpper ns)
    isUpper [] = False
    isUpper (c : _) = Char.isUpper c

    parenSymbol n = (if isSymbol n then PP.parens else id) $ toDoc n
    isSymbol (Name (Namespace ns) s) = isSymbolString (concat ns ++ s)

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

ppInfixOps :: (a -> Maybe (InfixOp,a,a)) -> (Bool -> a -> PP.Doc) ->
              Bool -> a -> PP.Doc
ppInfixOps dest pp =
    go Nothing
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

  toStringWith :: PP.Style -> a -> String
  toStringWith style = PP.renderStyle style . toDoc

  toString :: a -> String
  toString = toStringWith style
    where
      style = PP.style {PP.lineLength = 80, PP.ribbonsPerLine = 1.0}

instance Printable PP.Doc where
  toDoc = id

instance Printable Integer where
  toDoc = PP.integer

instance (Printable a, Printable b) => Printable (a,b) where
  toDoc (x,y) = PP.parens (toDoc x <> PP.comma <+> toDoc y)

instance Printable a => Printable [a] where
  toDoc = PP.brackets . PP.fsep . PP.punctuate PP.comma . map toDoc

instance Printable a => Printable (Set a) where
  toDoc = PP.braces . PP.sep . PP.punctuate PP.comma . map toDoc . Set.toAscList

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

quoteNamespace :: Namespace -> PP.Doc
quoteNamespace (Namespace l) =
    PP.doubleQuotes $ PP.hcat $ PP.punctuate sep $ map escape l
  where
    escape = PP.hcat . map mk
    mk c = let d = PP.char c in if escapable c then esc <> d else d
    escapable = flip elem "\"\\."

    sep = PP.text "."
    esc = PP.char '\\'

quoteName :: Name -> PP.Doc
quoteName (Name (Namespace l) s) = quoteNamespace (Namespace (l ++ [s]))

-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

instance Printable TypeVar where
  toDoc = toDoc . TypeVar.dest

instance Printable TypeOp where
  toDoc = ppSymbolName . TypeOp.name

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

      normal = ppInfixOps destInfix basic True

      normals = PP.parens . PP.fsep . PP.punctuate PP.comma . map normal

      parens = PP.parens . normal

      -------------------------------------------------------------------------
      -- These grammar tables control type printing
      -------------------------------------------------------------------------

      infixTable =
          [--
           -- Primitives
           (TypeOp.funName, 1, RightAssoc, Nothing),
           --
           -- Pairs
           (TypeOp.productName, 3, RightAssoc, Nothing),
           --
           -- Sums
           (TypeOp.sumName, 2, RightAssoc, Nothing)]

      -------------------------------------------------------------------------
      -- Infix type operators
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

instance Printable TypeSubst where
  toDoc = toDoc . map mk . Map.toAscList . TypeSubst.dest
    where
      mk (v,ty) = toDoc v <+> PP.text "|->" <+> toDoc ty

-------------------------------------------------------------------------------
-- Terms
-------------------------------------------------------------------------------

instance Printable Const where
  toDoc = ppSymbolName . Const.name

instance Printable Var where
  toDoc = toDoc . Var.name

instance Printable Term where
  toDoc =
      normal
    where
      atom tm =
          case Term.dest tm of
            VarTerm v -> toDoc v
            ConstTerm c _ -> toDoc c
            _ -> parens tm

      comprehension tm =
          case destComprehension tm of
            Just (v,pat,prd) ->
                ppComprehension (map toDoc v) (normal pat) (normal prd)
            Nothing -> atom tm

      pair tm =
          case stripPair tm of
            ([],_) -> comprehension tm
            (xs,y) -> ppPair (map (negation False) xs ++ [negation True y])

      basic tm =
          case destNumeral tm of
            Just i -> PP.integer i
            Nothing -> pair tm

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

      infixTerm = ppInfixOps destInfix negation

      conditional rightmost tm =
          case stripCond tm of
            ([],_) -> infixTerm rightmost tm
            ((c,t) : cts, e) -> ppCond (infixTerm False)
                                  (infixTerm rightmost) c t cts e

      letTerm rightmost tm =
          case stripLet tm of
            ([],_) -> conditional rightmost tm
            (ves,t) -> ppLet application (conditional False)
                         (conditional rightmost) ves t

      normal = letTerm True

      parens = PP.parens . normal

      -------------------------------------------------------------------------
      -- These grammar tables control term printing
      -------------------------------------------------------------------------

      infixTable :: [(Name, Prec, Assoc, Maybe String)]
      infixTable =
          [--
           -- Booleans
           (Const.conjName, -1, RightAssoc, Nothing),
           (Const.disjName, -2, RightAssoc, Nothing),
           (Const.impName, -3, RightAssoc, Nothing),
           --
           -- Functions
           (Const.composeName, 4, LeftAssoc, Nothing),
           (Const.funpowName, 9, RightAssoc, Nothing),
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
           (Const.crossName, 7, LeftAssoc, Nothing),
           (Const.intersectName, 7, LeftAssoc, Nothing),
           (Const.differenceName, 6, LeftAssoc, Just "-"),
           (Const.unionName, 6, LeftAssoc, Nothing),
           (Const.insertName, 6, LeftAssoc, Nothing),
           (Const.deleteName, 6, LeftAssoc, Nothing),
           (Const.memberName, 3, NonAssoc, Just "in"),
           (Const.subsetName, 3, NonAssoc, Nothing),
           (Const.properSubsetName, 3, NonAssoc, Nothing),
           --
           --  List theory
           (Const.appendName, 5, RightAssoc, Nothing),
           (Const.consName, 5, RightAssoc, Nothing),
           --
           -- Real numbers
           (Const.powerRealName, 9, RightAssoc, Nothing),
           (Const.multRealName, 8, LeftAssoc, Nothing),
           (Const.divRealName, 8, LeftAssoc, Nothing),
           (Const.addRealName, 6, LeftAssoc, Nothing),
           (Const.subRealName, 6, LeftAssoc, Nothing),
           (Const.leRealName, 3, NonAssoc, Nothing),
           (Const.ltRealName, 3, NonAssoc, Nothing),
           (Const.geRealName, 3, NonAssoc, Nothing),
           (Const.gtRealName, 3, NonAssoc, Nothing)]

      quantifierTable :: [(Name, Maybe String)]
      quantifierTable =
          [(Const.selectName, Nothing),
           (Const.forallName, Nothing),
           (Const.existsName, Nothing),
           (Const.existsUniqueName, Nothing)]

      negationTable :: [(Name, Maybe String)]
      negationTable =
          [(Const.negName, Nothing)]

      -------------------------------------------------------------------------
      -- Operators of a given arity
      -------------------------------------------------------------------------

      destUnaryOp :: Term -> Maybe (Const,Term)
      destUnaryOp tm = do
          (t,x) <- Term.destApp tm
          (c,_) <- Term.destConst t
          return (c,x)

      destBinaryOp :: Term -> Maybe (Const,Term,Term)
      destBinaryOp tm = do
          (t,y) <- Term.destApp tm
          (c,x) <- destUnaryOp t
          return (c,x,y)

      destTernaryOp :: Term -> Maybe (Const,Term,Term,Term)
      destTernaryOp tm = do
          (t,z) <- Term.destApp tm
          (c,x,y) <- destBinaryOp t
          return (c,x,y,z)

      -------------------------------------------------------------------------
      -- Infix operators
      -------------------------------------------------------------------------

      nameOp :: Name -> Maybe String -> String
      nameOp n x =
          case x of
            Just y -> y
            Nothing -> let Name _ y = n in y

      mkInfixOp :: (Name, Prec, Assoc, Maybe String) -> (Name,InfixOp)
      mkInfixOp (n,p,a,x) =
          (n, (p, a, flip (<+>) d))
        where
          s = nameOp n x
          t = PP.text s
          d = if isSymbolString s then t else PP.char '`' <> t <> PP.char '`'

      eqInfixOp :: InfixOp
      eqInfixOp = snd $ mkInfixOp (Const.eqName, 3, NonAssoc, Nothing)

      iffInfixOp :: InfixOp
      iffInfixOp = snd $ mkInfixOp (Const.eqName, -4, NonAssoc, Just "<=>")

      infixOps :: Map Name InfixOp
      infixOps = Map.fromList $ map mkInfixOp infixTable

      destInfix :: Term -> Maybe (InfixOp,Term,Term)
      destInfix tm = do
          (c,x,y) <- destBinaryOp tm
          i <- lookupOp (Term.typeOf x) (Const.name c)
          return (i,x,y)
        where
          lookupOp ty n =
              if n /= Const.eqName then Map.lookup n infixOps
              else if Type.isBool ty then Just iffInfixOp
              else Just eqInfixOp

      isInfix :: Term -> Bool
      isInfix = isJust . destInfix

      -------------------------------------------------------------------------
      -- Prefix operators
      -------------------------------------------------------------------------

      mkPrefixOp :: (Name, Maybe String) -> (Name,PrefixOp)
      mkPrefixOp (n,x) =
          (n, attach $ PP.text s)
        where
          s = nameOp n x
          attach = case reverse s of
                     c : _ | isSymbolChar c -> (<>)
                     _ -> (<+>)

      -------------------------------------------------------------------------
      -- Generalized lambda abstractions
      -------------------------------------------------------------------------

      destForall :: Term -> Maybe (Var,Term)
      destForall tm = do
          (c,t) <- destUnaryOp tm
          (v,b) <- Term.destAbs t
          guard (Const.name c == Const.forallName)
          return (v,b)

      stripForall :: Term -> ([Var],Term)
      stripForall tm =
          case destForall tm of
            Just (v,t) -> (v : vs, b) where (vs,b) = stripForall t
            Nothing -> ([],tm)

      destAbs :: Term -> Maybe (Term,Term)
      destAbs tm =
          case Term.destAbs tm of
            Just (v,t) -> Just (Term.mkVar v, t)
            Nothing -> do
              (f,t0) <- Term.destSelect tm
              let (vl,t1) = stripForall t0
              guard (Var.notFreeIn f vl)
              (t2,body) <- Term.destEq t1
              (f',pat) <- Term.destApp t2
              guard (Term.eqVar f f')
              guard (Set.toAscList (Var.free pat) == vl)
              guard (Var.notFreeIn f body)
              return (pat,body)

      lambda :: PrefixOp
      lambda = snd $ mkPrefixOp (undefined, Just "\\")

      stripLambda :: Term -> Maybe (PrefixOp,[Term],Term)
      stripLambda tm = do
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

      destQuantifier :: Term -> Maybe (Const,Term,Term)
      destQuantifier tm = do
          (c,vb) <- destUnaryOp tm
          (v,b) <- destAbs vb
          return (c,v,b)

      stripQuantifier :: Term -> Maybe (PrefixOp,[Term],Term)
      stripQuantifier tm = do
          (c,v,t) <- destQuantifier tm
          q <- Map.lookup (Const.name c) quantifiers
          let (vs,b) = strip c t
          return (q, v : vs, b)
        where
          strip c t =
              case destQuantifier t of
                Just (c',v,u) | c' == c -> (v : vs, b) where (vs,b) = strip c u
                _ -> ([],t)

      -------------------------------------------------------------------------
      -- Binders
      -------------------------------------------------------------------------

      destBinder :: Term -> Maybe (PrefixOp,[Term],Term)
      destBinder tm =
          case stripLambda tm of
            Just b -> Just b
            Nothing -> stripQuantifier tm

      isBinder :: Term -> Bool
      isBinder = isJust . destBinder

      ppBoundVars :: [PP.Doc] -> PP.Doc
      ppBoundVars =
          \v -> PP.fsep v <> dot
        where
          dot = PP.char '.'

      ppBinder :: PrefixOp -> [PP.Doc] -> PP.Doc -> PP.Doc
      ppBinder b v t = b $ PP.sep [ppBoundVars v, t]

      -------------------------------------------------------------------------
      -- Negation operators
      -------------------------------------------------------------------------

      negations :: Map Name PrefixOp
      negations = Map.fromList $ map mkPrefixOp negationTable

      destNegation :: Term -> Maybe (PrefixOp,Term)
      destNegation tm = do
          (c,t) <- destUnaryOp tm
          p <- Map.lookup (Const.name c) negations
          return (p,t)

      isNegation :: Term -> Bool
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
          (c,x,y,z) <- destTernaryOp tm
          guard (Const.name c == Const.condName)
          return (x,y,z)

      isCond :: Term -> Bool
      isCond = isJust . destCond

      stripCond :: Term -> ([(Term,Term)],Term)
      stripCond tm =
          case destCond tm of
            Just (c,t,u) -> ((c,t) : cts, e) where (cts,e) = stripCond u
            Nothing -> ([],tm)

      ppCond :: (Term -> PP.Doc) -> (Term -> PP.Doc) ->
                Term -> Term -> [(Term,Term)] -> Term -> PP.Doc
      ppCond pp ppe =
          \c t cts e ->
            PP.sep (ifThen c t : map elseIfThen cts ++ [elseBranch e])
        where
          ifThen c t =
              PP.text "if" <+> PP.sep [pp c, PP.text "then" <+> pp t]

          elseIfThen (c,t) =
              PP.text "else" <+> PP.sep [PP.text "if" <+> pp c,
                                         PP.text "then" <+> pp t]

          elseBranch e = PP.text "else" <+> ppe e

      -------------------------------------------------------------------------
      -- Lets
      -------------------------------------------------------------------------

      destLet :: Term -> Maybe (Term,Term,Term)
      destLet tm = do
          (vt,e) <- Term.destApp tm
          (v,t) <- destAbs vt
          return (v,e,t)

      isLet :: Term -> Bool
      isLet = isJust . destLet

      stripLet :: Term -> ([(Term,Term)],Term)
      stripLet tm =
          case destLet tm of
            Just (v,e,u) -> ((v,e) : ves, t) where (ves,t) = stripLet u
            Nothing -> ([],tm)

      ppLet :: (Term -> PP.Doc) -> (Term -> PP.Doc) -> (Term -> PP.Doc) ->
               [(Term,Term)] -> Term -> PP.Doc
      ppLet ppv ppe pp =
          \ves t ->
            PP.sep (map letBind ves ++ [pp t])
        where
          letBind (v,e) =
              PP.text "let" <+> PP.sep [ppv v <+> PP.text "<-",
                                        ppe e <+> PP.text "in"]

      -------------------------------------------------------------------------
      -- Numerals
      -------------------------------------------------------------------------

      fromNaturals :: Set Name
      fromNaturals = Set.fromList
          [Const.fromNaturalRealName]

      destFromNatural :: Term -> Maybe Term
      destFromNatural tm = do
          (c,t) <- destUnaryOp tm
          guard (Set.member (Const.name c) fromNaturals)
          return t

      destMaybeFromNatural :: Term -> Term
      destMaybeFromNatural tm =
          case destFromNatural tm of
            Just t -> t
            Nothing -> tm

      isZero :: Term -> Bool
      isZero tm =
          case Term.destConst tm of
            Just (c,_) -> Const.name c == Const.zeroName
            Nothing -> False

      destBit :: Term -> Maybe (Bool,Term)
      destBit tm = do
          (c,t) <- destUnaryOp tm
          fmap (flip (,) t) $ bit (Const.name c)
        where
          bit n = if n == Const.bit0Name then Just False
                  else if n == Const.bit1Name then Just True
                  else Nothing

      destBits :: Term -> Maybe Integer
      destBits tm =
          if isZero tm then Just 0
          else do
            (b,t) <- destBit tm
            i <- destNumeral t
            bit b i
        where
          bit False 0 = Nothing
          bit b i = Just (2 * i + (if b then 1 else 0))

      destNumeral :: Term -> Maybe Integer
      destNumeral = destBits . destMaybeFromNatural

      isNumeral :: Term -> Bool
      isNumeral = isJust . destNumeral

      -------------------------------------------------------------------------
      -- Pairs
      -------------------------------------------------------------------------

      destPair :: Term -> Maybe (Term,Term)
      destPair tm = do
          (c,x,y) <- destBinaryOp tm
          guard (Const.name c == Const.pairName)
          return (x,y)

      isPair :: Term -> Bool
      isPair = isJust . destPair

      stripPair :: Term -> ([Term],Term)
      stripPair tm =
          case destPair tm of
            Just (x,t) -> (x : xs, y) where (xs,y) = stripPair t
            Nothing -> ([],tm)

      ppPair :: [PP.Doc] -> PP.Doc
      ppPair = PP.parens . PP.fsep . PP.punctuate PP.comma

      -------------------------------------------------------------------------
      -- Set comprehensions
      -------------------------------------------------------------------------

      destFromPredicate :: Term -> Maybe Term
      destFromPredicate tm = do
          (c,t) <- destUnaryOp tm
          guard (Const.name c == Const.fromPredicateName)
          return t

      destConj :: Term -> Maybe (Term,Term)
      destConj tm = do
          (c,x,y) <- destBinaryOp tm
          guard (Const.name c == Const.conjName)
          return (x,y)

      destExists :: Term -> Maybe (Var,Term)
      destExists tm = do
          (c,t) <- destUnaryOp tm
          (v,b) <- Term.destAbs t
          guard (Const.name c == Const.existsName)
          return (v,b)

      stripExists :: Term -> ([Var],Term)
      stripExists tm =
          case destExists tm of
            Just (v,t) -> (v : vs, b) where (vs,b) = stripExists t
            Nothing -> ([],tm)

      destComprehension :: Term -> Maybe ([Var],Term,Term)
      destComprehension tm = do
          t0 <- destFromPredicate tm
          (v,t1) <- Term.destAbs t0
          let (vl,t2) = stripExists t1
          guard (not (null vl))
          let vs = Set.fromList vl
          guard (length vl == Set.size vs)
          guard (Set.notMember v vs)
          (t3,prd) <- destConj t2
          (v',pat) <- Term.destEq t3
          guard (Term.eqVar v v')
          let fvs = Var.free pat
          guard (Set.notMember v fvs)
          guard (Var.notFreeIn v prd)
          guard (Set.isSubsetOf vs fvs)
          return (vl,pat,prd)

      isComprehension :: Term -> Bool
      isComprehension = isJust . destComprehension

      ppComprehension :: [PP.Doc] -> PP.Doc -> PP.Doc -> PP.Doc
      ppComprehension v pat prd =
          PP.lbrace <+>
          PP.sep [PP.sep [ppBoundVars v, pat <+> PP.text "|"], prd] <+>
          PP.rbrace

      -------------------------------------------------------------------------
      -- Function application
      -------------------------------------------------------------------------

      destGenApp :: Term -> Maybe (Term,Term)
      destGenApp tm = do
          guard (not $ isNumeral tm)
          guard (not $ isCond tm)
          guard (not $ isPair tm)
          guard (not $ isLet tm)
          guard (not $ isComprehension tm)
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
