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

import qualified System.Environment as Environment

import HOL.OpenTheory (readArticle,readPackages)
import qualified HOL.OpenTheory.Interpret as Interpret
import HOL.Parse
import HOL.Print
import HOL.Theory (Theory)
import qualified HOL.Theory as Theory

profileReadArticle :: IO Theory
profileReadArticle = do
    ths <- readArticle Theory.standard Interpret.empty "base.art"
    return $ Theory.fromThmSet ths

profileReadPackages :: IO Theory
profileReadPackages = do
    ts <- readPackages [fromStringUnsafe "base"]
    return $ Theory.unionList ts

main :: IO ()
main = do
    args <- Environment.getArgs
    thy <- case args of
             [] -> profileReadArticle
             ["package"] -> profileReadPackages
             _ -> error $ "bad arguments: " ++ show args
    putStrLn $ toString thy
    return ()
