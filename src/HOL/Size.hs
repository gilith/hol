{- |
module: $Header$
description: Measuring the size of values
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.Size
where

import qualified Data.List as List

-------------------------------------------------------------------------------
-- The type of sizes
-------------------------------------------------------------------------------

type Size = Integer

-------------------------------------------------------------------------------
-- The type of sizes
-------------------------------------------------------------------------------

class Sizable a where
  size :: a -> Size

instance Sizable a => Sizable [a] where
  size = List.foldl' add 0
    where add n x = n + size x
