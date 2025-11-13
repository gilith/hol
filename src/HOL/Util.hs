{- |
module: $Header$
description: Utility functions
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.Util
where

-------------------------------------------------------------------------------
-- Creating unsafe versions of functions
-------------------------------------------------------------------------------

mkUnsafe :: String -> Maybe a -> a
mkUnsafe _ (Just x) = x
mkUnsafe s Nothing = error (s ++ " failed")

mkUnsafe1 :: String -> (a -> Maybe b) -> a -> b
mkUnsafe1 s f = mkUnsafe s . f

mkUnsafe2 :: String -> (a -> b -> Maybe c) -> a -> b -> c
mkUnsafe2 s f = mkUnsafe1 s . f

mkUnsafe3 :: String -> (a -> b -> c -> Maybe d) -> a -> b -> c -> d
mkUnsafe3 s f = mkUnsafe2 s . f

mkUnsafe4 :: String -> (a -> b -> c -> d -> Maybe e) -> a -> b -> c -> d -> e
mkUnsafe4 s f = mkUnsafe3 s . f

mkUnsafe5 :: String -> (a -> b -> c -> d -> e -> Maybe f) -> a -> b -> c -> d -> e -> f
mkUnsafe5 s f = mkUnsafe4 s . f
