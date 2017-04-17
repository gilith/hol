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

equalName :: Name -> TypeVar -> Bool
equalName n (TypeVar m) = m == n

-------------------------------------------------------------------------------
-- Named type variables
-------------------------------------------------------------------------------

alpha :: TypeVar
alpha = mk (mkGlobal "A")

-------------------------------------------------------------------------------
-- Extracting type variables
-------------------------------------------------------------------------------

data Vars = Vars (Set TypeVar) (Set Type) (Set Term)

emptyVars :: Vars
emptyVars = Vars Set.empty Set.empty Set.empty

setVars :: Vars -> Set TypeVar
setVars (Vars tvs _ _) = tvs

class HasVars a where
  addVars :: a -> Vars -> Vars

  vars :: a -> Set TypeVar
  vars x = setVars (addVars x emptyVars)

instance HasVars TypeVar where
  addVars tv (Vars tvs tys tms) = Vars (Set.insert tv tvs) tys tms

instance HasVars a => HasVars [a] where
  addVars xs vs = foldr addVars vs xs

instance HasVars a => HasVars (Set a) where
  addVars xs vs = Set.foldr addVars vs xs

instance HasVars TypeData where
  addVars (VarType v) vs = addVars v vs
  addVars (OpType _ tys) vs = addVars tys vs

instance HasVars Type where
  addVars ty vs =
      if marked then vs else mark $ addVars d vs
    where
      Type d _ = ty
      marked = Set.member ty tys where Vars _ tys _ = vs
      mark (Vars tvs tys tms) = Vars tvs (Set.insert ty tys) tms

instance HasVars Var where
  addVars (Var _ ty) vs = addVars ty vs

instance HasVars TermData where
  addVars (ConstTerm _ ty) = addVars ty
  addVars (VarTerm v) = addVars v
  addVars (AppTerm f x) = addVars f . addVars x
  addVars (AbsTerm v b) = addVars v . addVars b

instance HasVars Term where
  addVars tm vs =
      if marked then vs else mark $ addVars d vs
    where
      Term d _ _ = tm
      marked = Set.member tm tms where Vars _ _ tms = vs
      mark (Vars tvs tys tms) = Vars tvs tys (Set.insert tm tms)
