{- |
module: $Header$
description: Higher order logic terms
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.Term
where

import Data.Maybe (isJust)
import qualified Data.Map as Map
import System.IO.Unsafe (unsafePerformIO)
import System.Mem.StableName (makeStableName)

import qualified HOL.Const as Const
import HOL.Data
import qualified HOL.TermData as TermData
import qualified HOL.Type as Type
import qualified HOL.TypeVar as TypeVar
import qualified HOL.Var as Var

-------------------------------------------------------------------------------
-- Constructors and destructors
-------------------------------------------------------------------------------

dest :: Term -> TermData
dest (Term d _ _ _ _ _) = d

mk :: TermData -> Term
mk d =
    Term d i sz ty tvs fvs
  where
    i = unsafePerformIO (makeStableName $! d)
    sz = TermData.size d
    ty = TermData.typeOf d
    tvs = TypeVar.vars d
    fvs = Var.free d

-- Constants

mkConst :: Const -> Type -> Term
mkConst c = mk . TermData.mkConst c

destConst :: Term -> Maybe (Const,Type)
destConst = TermData.destConst . dest

isConst :: Term -> Bool
isConst = isJust . destConst

destGivenConst :: Const -> Term -> Maybe Type
destGivenConst c = TermData.destGivenConst c . dest

isGivenConst :: Const -> Term -> Bool
isGivenConst c = isJust . destGivenConst c

-- Variables

mkVar :: Var -> Term
mkVar = mk . TermData.mkVar

destVar :: Term -> Maybe Var
destVar = TermData.destVar . dest

isVar :: Term -> Bool
isVar = isJust . destVar

eqVar :: Var -> Term -> Bool
eqVar v = TermData.eqVar v . dest

-- Function application

mkApp :: Term -> Term -> Maybe Term
mkApp f x = fmap mk $ TermData.mkApp f x

mkAppUnsafe :: Term -> Term -> Term
mkAppUnsafe f x =
    case mkApp f x of
      Just tm -> tm
      Nothing -> error "HOL.Term.mkApp failed"

destApp :: Term -> Maybe (Term,Term)
destApp = TermData.destApp . dest

isApp :: Term -> Bool
isApp = isJust . destApp

rator :: Term -> Maybe Term
rator = fmap fst . destApp

rand :: Term -> Maybe Term
rand = fmap snd . destApp

land :: Term -> Maybe Term
land tm = do
    f <- rator tm
    rand f

listMkApp :: Term -> [Term] -> Maybe Term
listMkApp tm [] = Just tm
listMkApp f (x : xs) = do
    fx <- mkApp f x
    listMkApp fx xs

listMkAppUnsafe :: Term -> [Term] -> Term
listMkAppUnsafe f xs =
    case listMkApp f xs of
      Just tm -> tm
      Nothing -> error "HOL.Term.listMkApp failed"

stripApp :: Term -> (Term,[Term])
stripApp =
    go []
  where
    go xs tm =
        case destApp tm of
          Nothing -> (tm,xs)
          Just (f,x) -> go (x : xs) f

-- Lambda abstraction

mkAbs :: Var -> Term -> Term
mkAbs v b = mk $ TermData.mkAbs v b

destAbs :: Term -> Maybe (Var,Term)
destAbs = TermData.destAbs . dest

isAbs :: Term -> Bool
isAbs = isJust . destAbs

listMkAbs :: [Var] -> Term -> Term
listMkAbs [] tm = tm
listMkAbs (v : vs) b = mkAbs v $ listMkAbs vs b

stripAbs :: Term -> ([Var],Term)
stripAbs tm =
    case destAbs tm of
      Nothing -> ([],tm)
      Just (v,t) -> (v : vs, b) where (vs,b) = stripAbs t

-------------------------------------------------------------------------------
-- Size is measured as the number of TermData constructors
-------------------------------------------------------------------------------

size :: Term -> Size
size (Term _ _ s _ _ _) = s

-------------------------------------------------------------------------------
-- The type of a (well-formed) term
-------------------------------------------------------------------------------

typeOf :: Term -> Type
typeOf (Term _ _ _ ty _ _) = ty

isBool :: Term -> Bool
isBool = Type.isBool . typeOf

sameType :: Term -> Term -> Bool
sameType tm1 tm2 = typeOf tm1 == typeOf tm2

sameTypeVar :: Var -> Term -> Bool
sameTypeVar v tm = Var.typeOf v == typeOf tm

-------------------------------------------------------------------------------
-- A total order on terms modulo alpha-equivalence
-------------------------------------------------------------------------------

alphaCompare :: Term -> Term -> Ordering
alphaCompare =
    tcmp 0 True bvEmpty bvEmpty
  where
    bvEmpty :: Map.Map Var Int
    bvEmpty = Map.empty

    tcmp n bvEq bv1 bv2 tm1 tm2 =
        if bvEq && iEq tm1 tm2 then EQ
        else case compare (size tm1) (size tm2) of
               LT -> LT
               EQ -> dcmp n bvEq bv1 bv2 (dest tm1) (dest tm2)
               GT -> GT

    iEq (Term _ i1 _ _ _ _) (Term _ i2 _ _ _ _) = i1 == i2

    dcmp _ _ bv1 bv2 (VarTerm v1) (VarTerm v2) =
        case (Map.lookup v1 bv1, Map.lookup v2 bv2) of
          (Nothing,Nothing) -> compare v1 v2
          (Just _, Nothing) -> LT
          (Nothing, Just _) -> GT
          (Just i1, Just i2) -> compare i1 i2

    dcmp n bvEq bv1 bv2 (AbsTerm v1 b1) (AbsTerm v2 b2) =
        case compare ty1 ty2 of
          LT -> LT
          EQ -> tcmp n' bvEq' bv1' bv2' b1 b2
          GT -> GT
      where
        (n1,ty1) = Var.dest v1
        (n2,ty2) = Var.dest v2
        n' = n + 1
        bvEq' = bvEq && n1 == n2
        bv1' = Map.insert v1 n bv1
        bv2' = if bvEq' then bv1' else Map.insert v2 n bv2

    dcmp n bvEq bv1 bv2 (AppTerm f1 x1) (AppTerm f2 x2) =
        case tcmp n bvEq bv1 bv2 f1 f2 of
          LT -> LT
          EQ -> tcmp n bvEq bv1 bv2 x1 x2
          GT -> GT

    dcmp _ _ _ _ d1 d2 = compare d1 d2

alphaEqual :: Term -> Term -> Bool
alphaEqual tm1 tm2 = alphaCompare tm1 tm2 == EQ

-------------------------------------------------------------------------------
-- Primitive constants
-------------------------------------------------------------------------------

-- Equality

mkEqConst :: Type -> Term
mkEqConst a = mkConst Const.eq $ Type.mkEq a

destEqConst :: Term -> Maybe Type
destEqConst tm = do
    ty <- destGivenConst Const.eq tm
    Type.destEq ty

isEqConst :: Term -> Bool
isEqConst = isJust . destEqConst

mkEq :: Term -> Term -> Maybe Term
mkEq l r = listMkApp c [l,r] where c = mkEqConst (typeOf l)

mkEqUnsafe :: Term -> Term -> Term
mkEqUnsafe l r =
    case mkEq l r of
      Just tm -> tm
      Nothing -> error "HOL.Term.mkEq failed"

destEq :: Term -> Maybe (Term,Term)
destEq tm = do
    (el,r) <- destApp tm
    (e,l) <- destApp el
    if isEqConst e then Just (l,r) else Nothing

isEq :: Term -> Bool
isEq = isJust . destEq

lhs :: Term -> Maybe Term
lhs = fmap fst . destEq

rhs :: Term -> Maybe Term
rhs = fmap snd . destEq

mkRefl :: Term -> Term
mkRefl tm = mkEqUnsafe tm tm

destRefl :: Term -> Maybe Term
destRefl tm = do
    (l,r) <- destEq tm
    if l == r then Just l else Nothing

isRefl :: Term -> Bool
isRefl = isJust . destRefl

-- Hilbert's choice operator

mkSelectConst :: Type -> Term
mkSelectConst a = mkConst Const.select $ Type.mkSelect a

destSelectConst :: Term -> Maybe Type
destSelectConst tm = do
    ty <- destGivenConst Const.select tm
    Type.destSelect ty

isSelectConst :: Term -> Bool
isSelectConst = isJust . destSelectConst

mkSelect :: Var -> Term -> Term
mkSelect v b =
    mkAppUnsafe c (mkAbs v b)
  where
    c = mkSelectConst $ Var.typeOf v

destSelect :: Term -> Maybe (Var,Term)
destSelect tm = do
    (c,vb) <- destApp tm
    if isSelectConst c then destAbs vb else Nothing

isSelect :: Term -> Bool
isSelect = isJust . destSelect
