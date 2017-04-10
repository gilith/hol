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
-- Type variables
-------------------------------------------------------------------------------

alpha :: TypeVar
alpha = mk (mkGlobal "A")
