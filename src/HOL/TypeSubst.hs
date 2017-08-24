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
import Data.Set (Set)
import qualified Data.Set as Set
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
    norm v ty = not $ Type.eqVar v ty

dest :: TypeSubst -> Map TypeVar Type
dest (TypeSubst m _) = m

fromList :: [(TypeVar,Type)] -> TypeSubst
fromList = mk . Map.fromList

empty :: TypeSubst
empty = fromList []

singleton :: TypeVar -> Type -> TypeSubst
singleton v ty = fromList [(v,ty)]

null :: TypeSubst -> Bool
null = Map.null . dest

-------------------------------------------------------------------------------
-- Equality
-------------------------------------------------------------------------------

instance Eq TypeSubst where
  sub1 == sub2 = dest sub1 == dest sub2

-------------------------------------------------------------------------------
-- Primitive type substitutions
-------------------------------------------------------------------------------

varSubst :: TypeVar -> TypeSubst -> Maybe Type
varSubst v (TypeSubst m _) = Map.lookup v m

dataSubst :: TypeData -> TypeSubst -> (Maybe Type, TypeSubst)
dataSubst (VarType v) s = (varSubst v s, s)
dataSubst (OpType t tys) s =
    (fmap (Type.mkOp t) tys', s')
  where
    (tys',s') = basicSubst tys s

-------------------------------------------------------------------------------
-- General type substitutions
-------------------------------------------------------------------------------

class CanSubst a where
  --
  -- This is the primitive substitution function for types to implement,
  -- which has the following properties:
  --  1. Can assume the substitution is not null
  --  2. Returns Nothing if the argument is unchanged by the substitution
  --  3. Returns the substitution with an updated type cache
  --
  basicSubst :: a -> TypeSubst -> (Maybe a, TypeSubst)

  --
  -- These substitution functions return Nothing if unchanged
  --
  sharingSubst :: a -> TypeSubst -> (Maybe a, TypeSubst)
  sharingSubst x s =
      if HOL.TypeSubst.null s then (Nothing,s) else basicSubst x s

  subst :: TypeSubst -> a -> Maybe a
  subst s x = fst $ sharingSubst x s

  --
  -- These substitution functions return their argument if unchanged
  --
  trySharingSubst :: a -> TypeSubst -> (a,TypeSubst)
  trySharingSubst x s = (fromMaybe x x', s') where (x',s') = sharingSubst x s

  trySubst :: TypeSubst -> a -> a
  trySubst s x = fromMaybe x (subst s x)

instance CanSubst a => CanSubst [a] where
  basicSubst [] s = (Nothing,s)
  basicSubst (h : t) s =
      (l',s'')
    where
      (h',s') = basicSubst h s
      (t',s'') = basicSubst t s'
      l' = case h' of
             Nothing -> fmap ((:) h) t'
             Just x -> Just (x : fromMaybe t t')

instance (Ord a, CanSubst a) => CanSubst (Set a) where
  basicSubst xs s =
      (xs',s')
    where
      xl = Set.toList xs
      (xl',s') = basicSubst xl s
      xs' = fmap Set.fromList xl'

instance CanSubst Type where
  basicSubst ty s =
      case Map.lookup ty c of
        Just ty' -> (ty',s)
        Nothing ->
            (ty', TypeSubst m (Map.insert ty ty' c'))
          where
            (ty', TypeSubst m c') = dataSubst (Type.dest ty) s
    where
      TypeSubst _ c = s

instance CanSubst Var where
  basicSubst (Var n ty) s =
      (fmap (Var n) ty', s')
    where
      (ty',s') = basicSubst ty s

-------------------------------------------------------------------------------
-- Composing type substitutions
-------------------------------------------------------------------------------

compose :: TypeSubst -> TypeSubst -> TypeSubst
compose sub1 sub2 | HOL.TypeSubst.null sub2 = sub1
compose sub1 sub2 | HOL.TypeSubst.null sub1 = sub2
compose sub1 sub2 | otherwise =
    mk $ fst $ Map.foldrWithKey inc (dest sub2, sub2) (dest sub1)
  where
    inc v1 t1 (m2,s2) = (m2',s2')
      where
        (t1',s2') = trySharingSubst t1 s2
        m2' = Map.insert v1 t1' m2
