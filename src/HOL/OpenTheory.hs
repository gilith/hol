{- |
module: $Header$
description: OpenTheory interface
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.OpenTheory
where

import Data.Set (Set)

import qualified HOL.OpenTheory.Article as Article
import HOL.OpenTheory.Interpret (Interpret)
import qualified HOL.OpenTheory.Package as Package
import HOL.Theory (Theory)
import HOL.Thm (Thm)

-------------------------------------------------------------------------------
-- Articles
-------------------------------------------------------------------------------

readArticle :: Theory -> Interpret -> FilePath -> IO (Set Thm)
readArticle = Article.readArticle

-------------------------------------------------------------------------------
-- Packages
-------------------------------------------------------------------------------

readPackages :: [Package.Name] -> IO [Theory]
readPackages = Package.readList
