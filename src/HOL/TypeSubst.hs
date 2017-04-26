{- |
module: $Header$
description: Higher order logic type substitutions
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.TypeSubst
where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import HOL.Data
import qualified HOL.Type as Type

-------------------------------------------------------------------------------
-- Type substitutions
-------------------------------------------------------------------------------

data TypeSubst = TypeSubst (Map TypeVar Type) (Map Type (Maybe Type))

-------------------------------------------------------------------------------
-- Constructors and destructors
-------------------------------------------------------------------------------

mk :: Map TypeVar Type -> TypeSubst
mk m =
    TypeSubst (Map.filterWithKey norm m) Map.empty
  where
    norm v ty = not $ Type.equalVar v ty

dest :: TypeSubst -> Map TypeVar Type
dest (TypeSubst m _) = m

fromList :: [(TypeVar,Type)] -> TypeSubst
fromList = mk . Map.fromList

-------------------------------------------------------------------------------
-- Primitive substitutions
-------------------------------------------------------------------------------

varSubst :: TypeVar -> TypeSubst -> Maybe Type
varSubst v (TypeSubst m _) = Map.lookup v m

dataSubst :: TypeData -> TypeSubst -> (Maybe Type, TypeSubst)
dataSubst (VarType v) s = (varSubst v s, s)
dataSubst (OpType t tys) s =
    (fmap (Type.mkOp t) tys', s')
  where
    (tys',s') = sharingSubst tys s

-------------------------------------------------------------------------------
-- General substitutions
-------------------------------------------------------------------------------

class CanSubst a where
  -- these substitution functions return Nothing if unchanged
  sharingSubst :: a -> TypeSubst -> (Maybe a, TypeSubst)

  subst :: TypeSubst -> a -> Maybe a
  subst s x = fst $ sharingSubst x s

  -- these substitution functions return their argument if unchanged
  trySharingSubst :: a -> TypeSubst -> (a,TypeSubst)
  trySharingSubst x s =
      (fromMaybe x y, s')
    where
      (y,s') = sharingSubst x s

  trySubst :: TypeSubst -> a -> a
  trySubst s x = fromMaybe x (subst s x)

instance CanSubst a => CanSubst [a] where
  sharingSubst [] s = (Nothing,s)
  sharingSubst (h : t) s =
      (l',s'')
    where
      (h',s') = sharingSubst h s
      (t',s'') = sharingSubst t s'
      l' = case h' of
             Nothing -> fmap ((:) h) t'
             Just x -> Just (x : fromMaybe t t')

instance CanSubst Type where
  sharingSubst ty s =
      case Map.lookup ty c of
        Just ty' -> (ty',s)
        Nothing ->
            (ty', TypeSubst m (Map.insert ty ty' c'))
          where
            (ty', TypeSubst m c') = dataSubst (Type.dest ty) s
    where
      TypeSubst _ c = s

instance CanSubst Var where
  sharingSubst (Var n ty) s =
      (fmap (Var n) ty', s')
    where
      (ty',s') = sharingSubst ty s
