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

import qualified Data.Foldable as Foldable
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
-- Collecting constants
-------------------------------------------------------------------------------

class HasConsts a where
  consts :: a -> Set Const

instance HasConsts Const where
  consts = Set.singleton

instance HasConsts a => HasConsts [a] where
  consts = Foldable.foldMap consts

instance HasConsts a => HasConsts (Set a) where
  consts = Foldable.foldMap consts

instance HasConsts TermData where
  consts (ConstTerm c _) = consts c
  consts (VarTerm _) = Set.empty
  consts (AppTerm f x) = Set.union (consts f) (consts x)
  consts (AbsTerm _ b) = consts b

instance HasConsts Term where
  consts (Term d _ _ _ _) = consts d

-------------------------------------------------------------------------------
-- Primitive constants
-------------------------------------------------------------------------------

-- Equality

eq :: Const
eq = mkUndef (mkGlobal "=")

-- Hilbert's indefinite choice operator

select :: Const
select = mkUndef (mkGlobal "select")

-- All primitive constants

primitives :: Set Const
primitives = Set.fromList [eq,select]
