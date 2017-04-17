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
import HOL.Name
import HOL.Size
import qualified HOL.Type as Type
import qualified HOL.TypeVar as TypeVar
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

-------------------------------------------------------------------------------
-- Axioms
-------------------------------------------------------------------------------

axiomOfExtensionality :: Term
axiomOfExtensionality =
    case axiom of
      Just tm -> tm
      Nothing -> error "axiomOfExtensionality shouldn't fail"
  where
    axiom = do
        let ty0 = Type.mkVar $ TypeVar.mk $ mkGlobal "A"
        let ty1 = Type.mkVar $ TypeVar.mk $ mkGlobal "B"
        let ty2 = Type.mkFun ty0 ty1
        let ty3 = Type.bool
        let ty4 = Type.mkFun ty2 ty3
        let v0 = Var.mk (mkGlobal "a") ty4
        let v1 = Var.mk (mkGlobal "b") ty2
        let v2 = Var.mk (mkGlobal "c") ty3
        let v3 = Var.mk (mkGlobal "d") ty2
        let v4 = Var.mk (mkGlobal "e") ty0
        let tm0 = mkVar v0
        let tm1 = mkVar v2
        let tm2 = mkAbs v2 tm1
        let tm3 = mkRefl tm2
        let tm4 = mkAbs v1 tm3
        tm5 <- mkEq tm0 tm4
        let tm6 = mkAbs v0 tm5
        let tm7 = mkVar v3
        let tm8 = mkVar v4
        tm9 <- mkApp tm7 tm8
        let tm10 = mkAbs v4 tm9
        tm11 <- mkEq tm10 tm7
        let tm12 = mkAbs v3 tm11
        tm13 <- mkApp tm6 tm12
        return tm13

axiomOfChoice :: Term
axiomOfChoice =
    case axiom of
      Just tm -> tm
      Nothing -> error "axiomOfChoice shouldn't fail"
  where
    axiom = do
        let ty0 = Type.mkVar $ TypeVar $ mkGlobal "A"
        let ty1 = Type.bool
        let ty2 = Type.mkFun ty0 ty1
        let ty3 = Type.mkFun ty2 ty1
        let ty4 = Type.mkFun ty1 ty1
        let ty5 = Type.mkFun ty1 ty4
        let v0 = Var.mk (mkGlobal "a") ty3
        let v1 = Var.mk (mkGlobal "b") ty2
        let v2 = Var.mk (mkGlobal "c") ty1
        let v3 = Var.mk (mkGlobal "d") ty2
        let v4 = Var.mk (mkGlobal "e") ty2
        let v5 = Var.mk (mkGlobal "f") ty0
        let v6 = Var.mk (mkGlobal "g") ty0
        let v7 = Var.mk (mkGlobal "h") ty1
        let v8 = Var.mk (mkGlobal "i") ty1
        let v9 = Var.mk (mkGlobal "j") ty1
        let v10 = Var.mk (mkGlobal "k") ty1
        let v11 = Var.mk (mkGlobal "l") ty5
        let v12 = Var.mk (mkGlobal "m") ty5
        let tm0 = mkVar v0
        let tm1 = mkVar v2
        let tm2 = mkAbs v2 tm1
        let tm3 = mkRefl tm2
        let tm4 = mkAbs v1 tm3
        tm5 <- mkEq tm0 tm4
        let tm6 = mkAbs v0 tm5
        let tm7 = mkVar v4
        let tm8 = mkAbs v5 tm3
        tm9 <- mkEq tm7 tm8
        let tm10 = mkAbs v4 tm9
        let tm11 = mkVar v11
        let tm12 = mkVar v9
        tm13 <- mkApp tm11 tm12
        let tm14 = mkVar v10
        tm15 <- mkApp tm13 tm14
        let tm16 = mkAbs v11 tm15
        let tm17 = mkVar v12
        tm18 <- mkApp tm17 tm3
        tm19 <- mkApp tm18 tm3
        let tm20 = mkAbs v12 tm19
        tm21 <- mkEq tm16 tm20
        let tm22 = mkAbs v10 tm21
        let tm23 = mkAbs v9 tm22
        let tm24 = mkVar v7
        tm25 <- mkApp tm23 tm24
        let tm26 = mkVar v8
        tm27 <- mkApp tm25 tm26
        tm28 <- mkEq tm27 tm24
        let tm29 = mkAbs v8 tm28
        let tm30 = mkAbs v7 tm29
        let tm31 = mkVar v3
        let tm32 = mkVar v6
        tm33 <- mkApp tm31 tm32
        tm34 <- mkApp tm30 tm33
        let tm35 = mkSelectConst ty0
        tm36 <- mkApp tm35 tm31
        tm37 <- mkApp tm31 tm36
        tm38 <- mkApp tm34 tm37
        let tm39 = mkAbs v6 tm38
        tm40 <- mkApp tm10 tm39
        let tm41 = mkAbs v3 tm40
        tm42 <- mkApp tm6 tm41
        return tm42

axiomOfInfinity :: Term
axiomOfInfinity =
    case axiom of
      Just tm -> tm
      Nothing -> error "axiomOfInfinity shouldn't fail"
  where
    axiom = do
        let ty0 = Type.ind
        let ty1 = Type.mkFun ty0 ty0
        let ty2 = Type.bool
        let ty3 = Type.mkFun ty1 ty2
        let ty4 = Type.mkFun ty2 ty2
        let ty5 = Type.mkFun ty2 ty4
        let ty6 = Type.mkFun ty0 ty2
        let v0 = Var.mk (mkGlobal "a") ty3
        let v1 = Var.mk (mkGlobal "b") ty4
        let v2 = Var.mk (mkGlobal "c") ty2
        let v3 = Var.mk (mkGlobal "d") ty2
        let v4 = Var.mk (mkGlobal "e") ty2
        let v5 = Var.mk (mkGlobal "f") ty2
        let v6 = Var.mk (mkGlobal "g") ty2
        let v7 = Var.mk (mkGlobal "h") ty2
        let v8 = Var.mk (mkGlobal "i") ty2
        let v9 = Var.mk (mkGlobal "j") ty5
        let v10 = Var.mk (mkGlobal "k") ty5
        let v11 = Var.mk (mkGlobal "l") ty3
        let v12 = Var.mk (mkGlobal "m") ty1
        let v13 = Var.mk (mkGlobal "n") ty1
        let v14 = Var.mk (mkGlobal "p") ty1
        let v15 = Var.mk (mkGlobal "q") ty6
        let v16 = Var.mk (mkGlobal "r") ty0
        let v17 = Var.mk (mkGlobal "s") ty0
        let v18 = Var.mk (mkGlobal "t") ty0
        let v19 = Var.mk (mkGlobal "u") ty2
        let v20 = Var.mk (mkGlobal "v") ty0
        let v21 = Var.mk (mkGlobal "w") ty6
        let v22 = Var.mk (mkGlobal "x") ty2
        let v23 = Var.mk (mkGlobal "y") ty0
        let v24 = Var.mk (mkGlobal "z") ty0
        let tm0 = mkVar v1
        let tm1 = mkVar v3
        let tm2 = mkAbs v3 tm1
        let tm3 = mkRefl tm2
        let tm4 = mkAbs v2 tm3
        tm5 <- mkEq tm0 tm4
        let tm6 = mkAbs v1 tm5
        let tm7 = mkVar v9
        let tm8 = mkVar v7
        tm9 <- mkApp tm7 tm8
        let tm10 = mkVar v8
        tm11 <- mkApp tm9 tm10
        let tm12 = mkAbs v9 tm11
        let tm13 = mkVar v10
        tm14 <- mkApp tm13 tm3
        tm15 <- mkApp tm14 tm3
        let tm16 = mkAbs v10 tm15
        tm17 <- mkEq tm12 tm16
        let tm18 = mkAbs v8 tm17
        let tm19 = mkAbs v7 tm18
        let tm20 = mkVar v5
        tm21 <- mkApp tm19 tm20
        let tm22 = mkVar v6
        tm23 <- mkApp tm21 tm22
        tm24 <- mkEq tm23 tm20
        let tm25 = mkAbs v6 tm24
        let tm26 = mkAbs v5 tm25
        let tm27 = mkVar v11
        let tm28 = mkAbs v12 tm3
        tm29 <- mkEq tm27 tm28
        let tm30 = mkAbs v11 tm29
        let tm31 = mkVar v0
        let tm32 = mkVar v13
        tm33 <- mkApp tm31 tm32
        tm34 <- mkApp tm26 tm33
        let tm35 = mkVar v4
        tm36 <- mkApp tm34 tm35
        let tm37 = mkAbs v13 tm36
        tm38 <- mkApp tm30 tm37
        tm39 <- mkApp tm26 tm38
        tm40 <- mkApp tm39 tm35
        let tm41 = mkAbs v4 tm40
        tm42 <- mkApp tm6 tm41
        let tm43 = mkAbs v0 tm42
        let tm44 = mkVar v15
        let tm45 = mkAbs v16 tm3
        tm46 <- mkEq tm44 tm45
        let tm47 = mkAbs v15 tm46
        let tm48 = mkVar v14
        let tm49 = mkVar v17
        tm50 <- mkApp tm48 tm49
        let tm51 = mkVar v18
        tm52 <- mkApp tm48 tm51
        tm53 <- mkEq tm50 tm52
        tm54 <- mkApp tm26 tm53
        tm55 <- mkEq tm49 tm51
        tm56 <- mkApp tm54 tm55
        let tm57 = mkAbs v18 tm56
        tm58 <- mkApp tm47 tm57
        let tm59 = mkAbs v17 tm58
        tm60 <- mkApp tm47 tm59
        tm61 <- mkApp tm19 tm60
        let tm62 = mkVar v19
        tm63 <- mkApp tm26 tm62
        tm64 <- mkApp tm6 tm2
        tm65 <- mkApp tm63 tm64
        let tm66 = mkAbs v19 tm65
        let tm67 = mkVar v21
        let tm68 = mkVar v23
        tm69 <- mkApp tm67 tm68
        tm70 <- mkApp tm26 tm69
        let tm71 = mkVar v22
        tm72 <- mkApp tm70 tm71
        let tm73 = mkAbs v23 tm72
        tm74 <- mkApp tm47 tm73
        tm75 <- mkApp tm26 tm74
        tm76 <- mkApp tm75 tm71
        let tm77 = mkAbs v22 tm76
        tm78 <- mkApp tm6 tm77
        let tm79 = mkAbs v21 tm78
        let tm80 = mkVar v20
        let tm81 = mkVar v24
        tm82 <- mkApp tm48 tm81
        tm83 <- mkEq tm80 tm82
        let tm84 = mkAbs v24 tm83
        tm85 <- mkApp tm79 tm84
        let tm86 = mkAbs v20 tm85
        tm87 <- mkApp tm47 tm86
        tm88 <- mkApp tm66 tm87
        tm89 <- mkApp tm61 tm88
        let tm90 = mkAbs v14 tm89
        tm91 <- mkApp tm43 tm90
        return tm91
