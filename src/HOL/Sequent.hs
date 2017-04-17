{- |
module: $Header$
description: Higher order logic sequents
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.Sequent
where

import qualified Data.Foldable as Foldable
import Data.Set (Set)
import HOL.AlphaTerm (AlphaTerm)
import qualified HOL.AlphaTerm as AlphaTerm

-------------------------------------------------------------------------------
-- Sequents
-------------------------------------------------------------------------------

data Sequent =
    Sequent
      {concl :: AlphaTerm,
       hyp :: Set AlphaTerm}
  deriving (Eq,Ord,Show)

-------------------------------------------------------------------------------
-- Invariant: Sequent hypotheses and conclusion are of type bool
-------------------------------------------------------------------------------

isBool :: Sequent -> Bool
isBool (Sequent {hyp = h, concl = c}) =
    Foldable.all AlphaTerm.isBool h && AlphaTerm.isBool c

-------------------------------------------------------------------------------
-- Constructors and destructors
-------------------------------------------------------------------------------

mk :: Set AlphaTerm -> AlphaTerm -> Maybe Sequent
mk h c =
    if isBool s then Just s else Nothing
  where
    s = Sequent {hyp = h, concl = c}

dest :: Sequent -> (Set AlphaTerm, AlphaTerm)
dest (Sequent {hyp = h, concl = c}) = (h,c)
