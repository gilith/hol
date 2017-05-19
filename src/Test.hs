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

import HOL.Print
import qualified HOL.Theory as Theory

main :: IO ()
main = do
  do thy <- Theory.readArticle Theory.standard "base.art"
     putStrLn $ toString thy
     return ()
