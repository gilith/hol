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
-- The size of a type as the number of constructors.
-------------------------------------------------------------------------------

size :: Type -> Size
size (Type _ s) = s

sizeList :: [Type] -> Size
sizeList =
    foldr addSize 0
  where
    addSize ty n = size ty + n

sizeData :: TypeData -> Size
sizeData (VarType _) = 1
sizeData (OpType _ tys) = sizeList tys + 1
