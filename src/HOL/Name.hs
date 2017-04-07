{- |
module: $Header$
description: Names in a hierarchical namespace
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.Name
where

import qualified Data.Maybe as Maybe

newtype Namespace =
    Namespace [String]
  deriving (Eq,Ord,Show)

data Name =
    Name Namespace String
  deriving (Eq,Ord,Show)

global :: Namespace
global = Namespace []

mkGlobal :: String -> Name
mkGlobal = Name global

destGlobal :: Name -> Maybe String
destGlobal (Name ns s) = if ns == global then Just s else Nothing

isGlobal :: Name -> Bool
isGlobal = Maybe.isJust . destGlobal
