{- |
module: Main
description: Querying the contents of OpenTheory packages
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}
module Main
  ( main )
where

import System.FilePath (isValid,takeDirectory,takeExtension)
import qualified System.Environment as Environment

import HOL.OpenTheory (readArticle,readPackages)
import qualified HOL.OpenTheory.Interpret as Interpret
import HOL.OpenTheory.Package (Name,NameVersion)
import qualified HOL.OpenTheory.Package as Package
import HOL.Parse
import HOL.Print
import HOL.Theory (Theory)
import qualified HOL.Theory as Theory

-------------------------------------------------------------------------------
-- An article file
-------------------------------------------------------------------------------

articleArg :: [String] -> Maybe FilePath
articleArg [f] | isValid f && takeExtension f == ".art" = Just f
articleArg _ = Nothing

articleThy :: FilePath -> IO Theory
articleThy f = do
    ths <- readArticle Theory.standard Interpret.empty f
    return $ Theory.fromThmSet ths

-------------------------------------------------------------------------------
-- A collection of packages
-------------------------------------------------------------------------------

packagesArg :: [String] -> Maybe [Name]
packagesArg = mapM fromString

packagesThy :: [Name] -> IO Theory
packagesThy = fmap Theory.unionList . readPackages

-------------------------------------------------------------------------------
-- A package file
-------------------------------------------------------------------------------

packageFileArg :: [String] -> Maybe FilePath
packageFileArg [f] | isValid f && takeExtension f == ".thy" = Just f
packageFileArg _ = Nothing

packageFileThy :: FilePath -> IO Theory
packageFileThy f = do
    pkg <- fromTextFile f
    req <- packagesThy (Package.requires pkg)
    let thy = Theory.union Theory.standard req
    let int = Interpret.empty
    let dir = takeDirectory f
    Package.readPackage thy int dir pkg

-------------------------------------------------------------------------------
-- A specific version of a package
-------------------------------------------------------------------------------

packageVersionArg :: [String] -> Maybe NameVersion
packageVersionArg [s] = fromString s
packageVersionArg _ = Nothing

packageVersionThy :: NameVersion -> IO Theory
packageVersionThy nv = do
    dir <- Package.directoryVersion nv
    packageFileThy (Package.packageFile dir (Package.name nv))

-------------------------------------------------------------------------------
-- Top-level
-------------------------------------------------------------------------------

usage :: String -> a
usage err =
    error $ err ++ "\n" ++ info
  where
    info =
      "Usage: hol-pkg INPUT\n" ++
      "where INPUT is one of the following forms:\n" ++
      "  FILE.art     : a proof article file\n" ++
      "  FILE.thy     : a theory package file\n" ++
      "  NAME-VERSION : a specific version of an installed theory package\n" ++
      "  NAME ...     : the latest installed version of a list of packages\n" ++
      "hol-pkg reads the INPUT to generate a set of theorems, which are\n" ++
      "pretty-printed to standard output together with the symbols they contain."

main :: IO ()
main = do
    args <- Environment.getArgs
    if null args then usage "no arguments" else return ()
    thy <- case articleArg args of
             Just f -> articleThy f
             Nothing ->
                 case packageFileArg args of
                   Just f -> packageFileThy f
                   Nothing ->
                     case packageVersionArg args of
                       Just nv -> packageVersionThy nv
                       Nothing ->
                           case packagesArg args of
                             Just ns -> packagesThy ns
                             Nothing -> usage $ "bad arguments: " ++ show args
    putStrLn $ toString thy
    return ()
