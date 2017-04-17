{- |
module: $Header$
description: Higher order logic constants
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.Const
where

import Data.Set (Set)
import qualified Data.Set as Set
import HOL.Name
import HOL.Data

-------------------------------------------------------------------------------
-- Constructors and destructors
-------------------------------------------------------------------------------

name :: Const -> Name
name (Const n _) = n

prov :: Const -> ConstProv
prov (Const _ p) = p

mkUndef :: Name -> Const
mkUndef n = Const n UndefConstProv

isUndef :: Const -> Bool
isUndef (Const _ p) = p == UndefConstProv

-------------------------------------------------------------------------------
-- Primitive constants
-------------------------------------------------------------------------------

-- Equality

eq :: Const
eq = mkUndef (mkGlobal "=")

-- Hilbert's indefinite choice operator

select :: Const
select = mkUndef (mkGlobal "select")

-- The standard primitives

primitives :: Set Const
primitives = Set.fromList [eq,select]
