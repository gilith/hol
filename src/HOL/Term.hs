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
import qualified HOL.Const as Const
import HOL.Data
import HOL.Size
import qualified HOL.Type as Type
import qualified HOL.Var as Var

-------------------------------------------------------------------------------
-- The type of a (well-formed) term
-------------------------------------------------------------------------------

typeOf :: Term -> Type
typeOf (Term _ _ ty) = ty

typeOfData :: TermData -> Type
typeOfData (ConstTerm _ ty) = ty
typeOfData (VarTerm v) = Var.typeOf v
typeOfData (AppTerm f _) =
    case Type.range (typeOf f) of
      Just ty -> ty
      Nothing -> error "ill-formed AppTerm"
typeOfData (AbsTerm v b) = Type.mkFun (Var.typeOf v) (typeOf b)

isBool :: Term -> Bool
isBool = Type.isBool . typeOf

-------------------------------------------------------------------------------
-- Constructors and destructors
-------------------------------------------------------------------------------

dest :: Term -> TermData
dest (Term d _ _) = d

mk :: TermData -> Term
mk d = Term d (size d) (typeOfData d)

-- Constants

mkConst :: Const -> Type -> Term
mkConst c ty = mk $ ConstTerm c ty

destConst :: Term -> Maybe (Const,Type)
destConst tm =
    case dest tm of
      ConstTerm c ty-> Just (c,ty)
      _ -> Nothing

isConst :: Term -> Bool
isConst = isJust . destConst

destGivenConst :: Const -> Term -> Maybe Type
destGivenConst c tm =
    case destConst tm of
      Just (d,ty) -> if d == c then Just ty else Nothing
      Nothing -> Nothing

isGivenConst :: Const -> Term -> Bool
isGivenConst c = isJust . destGivenConst c

-- Variables

mkVar :: Var -> Term
mkVar v = mk $ VarTerm v

destVar :: Term -> Maybe Var
destVar tm =
    case dest tm of
      VarTerm v -> Just v
      _ -> Nothing

isVar :: Term -> Bool
isVar = isJust . destVar

equalVar :: Var -> Term -> Bool
equalVar v tm =
    case destVar tm of
      Just w -> w == v
      Nothing -> False

-- Function application

mkApp :: Term -> Term -> Maybe Term
mkApp f x = do
    ty <- Type.domain (typeOf f)
    if typeOf x == ty then Just $ mk $ AppTerm f x else Nothing

destApp :: Term -> Maybe (Term,Term)
destApp tm =
    case dest tm of
      AppTerm f x -> Just (f,x)
      _ -> Nothing

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
mkAbs v b = mk $ AbsTerm v b

destAbs :: Term -> Maybe (Var,Term)
destAbs tm =
    case dest tm of
      AbsTerm v b -> Just (v,b)
      _ -> Nothing

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
-- A total order on terms modulo alpha-equivalence
-------------------------------------------------------------------------------

alphaCompare :: Term -> Term -> Ordering
alphaCompare =
    tcmp 0 True bvEmpty bvEmpty
  where
    bvEmpty :: Map.Map Var Int
    bvEmpty = Map.empty

    tcmp n bvEq bv1 bv2 tm1 tm2 =
        case compare (size tm1) (size tm2) of
          LT -> LT
          EQ -> dcmp n bvEq bv1 bv2 (dest tm1) (dest tm2)
          GT -> GT

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
mkRefl tm =
    case mkEq tm tm of
      Just r -> r
      Nothing -> error "mkRefl shouldn't fail"

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
    case mkApp c (mkAbs v b) of
      Just tm -> tm
      Nothing -> error "mkSelect shouldn't fail"
  where
    c = mkSelectConst $ Var.typeOf v

destSelect :: Term -> Maybe (Var,Term)
destSelect tm = do
    (c,vb) <- destApp tm
    if isSelectConst c then destAbs vb else Nothing

isSelect :: Term -> Bool
isSelect = isJust . destSelect
