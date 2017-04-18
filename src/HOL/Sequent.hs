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
import qualified Data.Set as Set
import HOL.TermAlpha (TermAlpha)
import qualified HOL.TermAlpha as TermAlpha

-------------------------------------------------------------------------------
-- Sequents
-------------------------------------------------------------------------------

data Sequent =
    Sequent
      {concl :: TermAlpha,
       hyp :: Set TermAlpha}
  deriving (Eq,Ord,Show)

-------------------------------------------------------------------------------
-- Constructors and destructors
-------------------------------------------------------------------------------

mk :: Set TermAlpha -> TermAlpha -> Maybe Sequent
mk h c =
    if b then Just sq else Nothing
  where
    b = Foldable.all TermAlpha.isBool h && TermAlpha.isBool c
    sq = Sequent {hyp = h, concl = c}

dest :: Sequent -> (Set TermAlpha, TermAlpha)
dest (Sequent {hyp = h, concl = c}) = (h,c)

-------------------------------------------------------------------------------
-- Standard axioms
-------------------------------------------------------------------------------

axiomOfExtensionality :: Sequent
axiomOfExtensionality =
    case mk Set.empty TermAlpha.axiomOfExtensionality of
      Just sq -> sq
      Nothing -> error "axiomOfExtensionality shouldn't fail"

axiomOfChoice :: Sequent
axiomOfChoice =
    case mk Set.empty TermAlpha.axiomOfChoice of
      Just sq -> sq
      Nothing -> error "axiomOfChoice shouldn't fail"

axiomOfInfinity :: Sequent
axiomOfInfinity =
    case mk Set.empty TermAlpha.axiomOfInfinity of
      Just sq -> sq
      Nothing -> error "axiomOfInfinity shouldn't fail"

standardAxioms :: Set Sequent
standardAxioms =
    Set.fromList
      [axiomOfExtensionality,
       axiomOfChoice,
       axiomOfInfinity]
