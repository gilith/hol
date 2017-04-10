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
-- Primitive type operators
-------------------------------------------------------------------------------

-- Booleans

bool :: TypeOp
bool = mkUndef (mkGlobal "bool")

-- Function spaces

fun :: TypeOp
fun = mkUndef (mkGlobal "->")

-- Individuals

ind :: TypeOp
ind = mkUndef (mkGlobal "ind")

-- The standard primitives

primitives :: Set TypeOp
primitives = Set.fromList [bool,fun,ind]
