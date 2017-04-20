{- |
module: $Header$
description: Higher order logic variables
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.Var
where

import qualified Data.Foldable as Foldable
import Data.Set (Set)
import qualified Data.Set as Set
import HOL.Name
import HOL.Data

-------------------------------------------------------------------------------
-- Constructors and destructors
-------------------------------------------------------------------------------

mk :: Name -> Type -> Var
mk = Var

dest :: Var -> (Name,Type)
dest (Var n ty) = (n,ty)

name :: Var -> Name
name (Var n _) = n

typeOf :: Var -> Type
typeOf (Var _ ty) = ty

-------------------------------------------------------------------------------
-- Free variables
-------------------------------------------------------------------------------

class HasFree a where
  free :: a -> Set Var

instance HasFree Var where
  free v = Set.singleton v

instance HasFree a => HasFree [a] where
  free = Foldable.foldMap free

instance HasFree a => HasFree (Set a) where
  free = Foldable.foldMap free

instance HasFree TermData where
  free (ConstTerm _ _) = Set.empty
  free (VarTerm v) = free v
  free (AppTerm f x) = Set.union (free f) (free x)
  free (AbsTerm v b) =
      if Set.member v bf then Set.delete v bf else bf
    where
      bf = free b

instance HasFree Term where
  free (Term _ _ _ _ vs) = vs
