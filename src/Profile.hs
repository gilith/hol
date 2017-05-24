{- |
module: Main
description: Profiling the higher order logic kernel
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}
module Main
  ( main )
where

import Data.Set (Set)

import qualified HOL.OpenTheory as OpenTheory
import HOL.Print
import qualified HOL.Theory as Theory
import HOL.Thm (Thm)

base :: IO (Set Thm)
base = OpenTheory.readArticle Theory.standard "base.art"

main :: IO ()
main = do
    ths <- base
    putStrLn $ toString ths
    return ()
