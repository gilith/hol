{- |
module: $Header$
description: Higher order logic type operators
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.TypeOp
where

import qualified Data.Foldable as Foldable
import Data.Set (Set)
import qualified Data.Set as Set
import HOL.Name
import HOL.Data

-------------------------------------------------------------------------------
-- Constructors and destructors
-------------------------------------------------------------------------------

name :: TypeOp -> Name
name (TypeOp n _) = n

prov :: TypeOp -> TypeOpProv
prov (TypeOp _ p) = p

mkUndef :: Name -> TypeOp
mkUndef n = TypeOp n UndefTypeOpProv

isUndef :: TypeOp -> Bool
isUndef (TypeOp _ p) = p == UndefTypeOpProv

-------------------------------------------------------------------------------
-- Collecting type operators
-------------------------------------------------------------------------------

class HasOps a where
  ops :: a -> Set TypeOp

instance HasOps TypeOp where
  ops = Set.singleton

instance HasOps a => HasOps [a] where
  ops = Foldable.foldMap ops

instance HasOps a => HasOps (Set a) where
  ops = Foldable.foldMap ops

instance HasOps TypeData where
  ops (VarType _) = Set.empty
  ops (OpType t tys) = Set.union (ops t) (ops tys)

instance HasOps Type where
  ops (Type d _ _ _) = ops d

instance HasOps Var where
  ops (Var _ ty) = ops ty

instance HasOps TermData where
  ops (ConstTerm _ ty) = ops ty
  ops (VarTerm v) = ops v
  ops (AppTerm f x) = Set.union (ops f) (ops x)
  ops (AbsTerm v b) = Set.union (ops v) (ops b)

instance HasOps Term where
  ops (Term d _ _ _ _ _) = ops d

-------------------------------------------------------------------------------
-- Primitive type operators
-------------------------------------------------------------------------------

-- Booleans

boolName :: Name
boolName = mkGlobal "bool"

bool :: TypeOp
bool = mkUndef boolName

-- Function spaces

funName :: Name
funName = mkGlobal "->"

fun :: TypeOp
fun = mkUndef funName

-- Individuals

indName :: Name
indName = mkGlobal "ind"

ind :: TypeOp
ind = mkUndef indName

-- All primitive type operators

primitives :: Set TypeOp
primitives = Set.fromList [bool,fun,ind]
