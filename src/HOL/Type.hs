{- |
module: $Header$
description: Higher order logic types
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.Type
where

import HOL.Name
import HOL.Data

-------------------------------------------------------------------------------
-- The size of a type is the number of TypeData constructors.
-------------------------------------------------------------------------------

size :: Type -> Size
size (Type s _) = s

sizeList :: [Type] -> Size
sizeList =
    foldr addSize 0
  where
    addSize ty n = size ty + n

sizeData :: TypeData -> Size
sizeData (VarType _) = 1
sizeData (OpType _ tys) = sizeList tys + 1

-------------------------------------------------------------------------------
-- Constructors and destructors.
-------------------------------------------------------------------------------

dest :: Type -> TypeData
dest (Type _ d) = d

mk :: TypeData -> Type
mk d = Type (sizeData d) d
