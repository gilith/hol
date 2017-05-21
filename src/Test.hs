{- |
module: Main
description: Testing the higher order logic kernel
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}
module Main
  ( main )
where

import Data.Set (Set)

import HOL.Print
import qualified HOL.Theory as Theory
import HOL.Thm (Thm)

base :: IO (Set Thm)
base = Theory.readArticle Theory.standard "base5.art"

main :: IO ()
main = do
    ths <- base
    putStrLn $ toString ths
    return ()
