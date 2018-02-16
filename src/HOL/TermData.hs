{- |
module: $Header$
description: Higher order logic term data
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.TermData
where

import Data.Maybe (isJust)
import HOL.Data
import qualified HOL.Type as Type
import qualified HOL.Var as Var

-------------------------------------------------------------------------------
-- Constructors and destructors
-------------------------------------------------------------------------------

-- Constants

mkConst :: Const -> Type -> TermData
mkConst = ConstTerm

destConst :: TermData -> Maybe (Const,Type)
destConst (ConstTerm c ty) = Just (c,ty)
destConst _ = Nothing

isConst :: TermData -> Bool
isConst = isJust . destConst

destGivenConst :: Const -> TermData -> Maybe Type
destGivenConst c d =
    case destConst d of
      Just (c',ty) -> if c' == c then Just ty else Nothing
      Nothing -> Nothing

isGivenConst :: Const -> TermData -> Bool
isGivenConst c = isJust . destGivenConst c

-- Variables

mkVar :: Var -> TermData
mkVar = VarTerm

destVar :: TermData -> Maybe Var
destVar (VarTerm v) = Just v
destVar _ = Nothing

isVar :: TermData -> Bool
isVar = isJust . destVar

eqVar :: Var -> TermData -> Bool
eqVar v d =
    case destVar d of
      Just w -> w == v
      Nothing -> False

-- Function application

mkApp :: Term -> Term -> Maybe TermData
mkApp f x = do
    ty <- Type.domain fty
    if xty == ty then Just $ AppTerm f x else Nothing
  where
    Term _ _ _ fty _ _ = f
    Term _ _ _ xty _ _ = x

destApp :: TermData -> Maybe (Term,Term)
destApp (AppTerm f x) = Just (f,x)
destApp _ = Nothing

isApp :: TermData -> Bool
isApp = isJust . destApp

-- Lambda abstraction

mkAbs :: Var -> Term -> TermData
mkAbs = AbsTerm

destAbs :: TermData -> Maybe (Var,Term)
destAbs (AbsTerm v b) = Just (v,b)
destAbs _ = Nothing

isAbs :: TermData -> Bool
isAbs = isJust . destAbs

-------------------------------------------------------------------------------
-- Size is measured as the number of TermData constructors
-------------------------------------------------------------------------------

size :: TermData -> Size
size (ConstTerm _ _) = 1
size (VarTerm _) = 1
size (AppTerm f x) =
    fsz + xsz
  where
    Term _ _ fsz _ _ _ = f
    Term _ _ xsz _ _ _ = x
size (AbsTerm _ b) =
    bsz + 1
  where
    Term _ _ bsz _ _ _ = b

-------------------------------------------------------------------------------
-- The type of a (well-formed) term
-------------------------------------------------------------------------------

typeOf :: TermData -> Type
typeOf (ConstTerm _ ty) = ty
typeOf (VarTerm v) = Var.typeOf v
typeOf (AppTerm f _) =
    case Type.range fty of
      Just ty -> ty
      Nothing -> error "HOL.TermData.typeOf: bad types in AppTerm"
  where
    Term _ _ _ fty _ _ = f
typeOf (AbsTerm v b) =
    Type.mkFun (Var.typeOf v) bty
  where
    Term _ _ _ bty _ _ = b

-------------------------------------------------------------------------------
-- Free variables in terms
-------------------------------------------------------------------------------

freeInMultiple :: Var -> TermData -> Bool
freeInMultiple v = go
  where
    go (ConstTerm _ _) = False
    go (VarTerm _) = False
    go (AppTerm f x) =
        case (Var.freeIn v f, Var.freeIn v x) of
          (True,True) -> True
          (True,False) -> go fd
          (False,True) -> go xd
          (False,False) -> False
      where
        Term fd _ _ _ _ _ = f
        Term xd _ _ _ _ _ = x
    go (AbsTerm w b) = w /= v && go bd
      where
        Term bd _ _ _ _ _ = b
