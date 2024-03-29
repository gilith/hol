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

import qualified Data.Char as Char
import qualified Data.List as List
import qualified Data.Maybe as Maybe
import Data.Set (Set)
import qualified Data.Set as Set

import HOL.Util (mkUnsafe1)

-------------------------------------------------------------------------------
-- Namespaces
-------------------------------------------------------------------------------

newtype Namespace =
    Namespace [String]
  deriving (Eq,Ord,Show)

-------------------------------------------------------------------------------
-- Names
-------------------------------------------------------------------------------

data Name =
    Name Namespace String
  deriving (Eq,Ord,Show)

-------------------------------------------------------------------------------
-- The global namespace (contains all type and term variable names)
-------------------------------------------------------------------------------

globalNamespace :: Namespace
globalNamespace = Namespace []

isGlobalNamespace :: Namespace -> Bool
isGlobalNamespace ns = ns == globalNamespace

mkGlobal :: String -> Name
mkGlobal = Name globalNamespace

destGlobal :: Name -> Maybe String
destGlobal (Name ns s) = if isGlobalNamespace ns then Just s else Nothing

destGlobalUnsafe :: Name -> String
destGlobalUnsafe = mkUnsafe1 "HOL.Name.destGlobal" destGlobal

isGlobal :: Name -> Bool
isGlobal = Maybe.isJust . destGlobal

mapGlobal :: (String -> String) -> Name -> Name
mapGlobal f (Name ns s) | isGlobalNamespace ns = Name ns (f s)
mapGlobal _ n = n

-------------------------------------------------------------------------------
-- Fresh names
-------------------------------------------------------------------------------

variantAvoiding :: Set Name -> Name -> Name
variantAvoiding avoid n =
    if Set.notMember n avoid then n else variant 0
  where
    Name ns bx = n
    b = List.dropWhileEnd isDigitOrPrime bx

    isDigitOrPrime :: Char -> Bool
    isDigitOrPrime c = Char.isDigit c || c == '\''

    variant :: Int -> Name
    variant i =
        if Set.notMember ni avoid then ni else variant (i + 1)
      where
        ni = Name ns bi
        bi = b ++ show i

freshSupply :: [Name]
freshSupply = map mkGlobal (stem ++ concat (map add [(0 :: Int) ..]))
  where
    add n = map (++ show n) stem
    stem = map (: []) "abcdefghijklmnpqrstuvwxyz"

-------------------------------------------------------------------------------
-- Standard namespaces
-------------------------------------------------------------------------------

-- Booleans

boolNamespace :: Namespace
boolNamespace = Namespace ["Data","Bool"]

-- Lists

listNamespace :: Namespace
listNamespace = Namespace ["Data","List"]

-- Products

pairNamespace :: Namespace
pairNamespace = Namespace ["Data","Pair"]

-- Sums

sumNamespace :: Namespace
sumNamespace = Namespace ["Data","Sum"]

-- Functions

functionNamespace :: Namespace
functionNamespace = Namespace ["Function"]

-- Natural numbers

naturalNamespace :: Namespace
naturalNamespace = Namespace ["Number","Natural"]

-- Real numbers

realNamespace :: Namespace
realNamespace = Namespace ["Number","Real"]

-- Sets

setNamespace :: Namespace
setNamespace = Namespace ["Set"]
