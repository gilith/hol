{- |
module: $Header$
description: Higher order logic type variables
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.TypeVar
where

import qualified Data.Foldable as Foldable
import Data.Set (Set)
import qualified Data.Set as Set
import HOL.Name
import HOL.Data

-------------------------------------------------------------------------------
-- Constructors and destructors
-------------------------------------------------------------------------------

mk :: Name -> TypeVar
mk = TypeVar

dest :: TypeVar -> Name
dest (TypeVar n) = n

eqName :: Name -> TypeVar -> Bool
eqName n (TypeVar m) = m == n

-------------------------------------------------------------------------------
-- Named type variables (used in standard axioms)
-------------------------------------------------------------------------------

alpha :: TypeVar
alpha = mk (mkGlobal "A")

beta :: TypeVar
beta = mk (mkGlobal "B")

-------------------------------------------------------------------------------
-- Collecting type variables
-------------------------------------------------------------------------------

class HasVars a where
  vars :: a -> Set TypeVar

instance HasVars TypeVar where
  vars = Set.singleton

instance HasVars a => HasVars [a] where
  vars = Foldable.foldMap vars

instance HasVars a => HasVars (Set a) where
  vars = Foldable.foldMap vars

instance HasVars TypeData where
  vars (VarType v) = vars v
  vars (OpType _ tys) = vars tys

instance HasVars Type where
  vars (Type _ _ _ vs) = vs

instance HasVars Var where
  vars (Var _ ty) = vars ty

instance HasVars TermData where
  vars (ConstTerm _ ty) = vars ty
  vars (VarTerm v) = vars v
  vars (AppTerm f x) = Set.union (vars f) (vars x)
  vars (AbsTerm v b) = Set.union (vars v) (vars b)

instance HasVars Term where
  vars (Term _ _ _ _ vs _) = vs
