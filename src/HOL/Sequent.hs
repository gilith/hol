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
import Data.Maybe (isNothing,fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified HOL.Const as Const
import qualified HOL.Subst as Subst
import HOL.TermAlpha (TermAlpha)
import qualified HOL.TermAlpha as TermAlpha
import qualified HOL.TypeOp as TypeOp
import qualified HOL.TypeVar as TypeVar
import HOL.Util (mkUnsafe1,mkUnsafe2)
import qualified HOL.Var as Var

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

mkUnsafe :: Set TermAlpha -> TermAlpha -> Sequent
mkUnsafe = mkUnsafe2 "HOL.Sequent.mk" mk

dest :: Sequent -> (Set TermAlpha, TermAlpha)
dest (Sequent {hyp = h, concl = c}) = (h,c)

nullHyp :: Sequent -> Bool
nullHyp = Set.null . hyp

mkNullHyp :: TermAlpha -> Maybe Sequent
mkNullHyp = mk Set.empty

mkNullHypUnsafe :: TermAlpha -> Sequent
mkNullHypUnsafe = mkUnsafe1 "HOL.Sequent.mkNullHyp" mkNullHyp

-------------------------------------------------------------------------------
-- Type variables
-------------------------------------------------------------------------------

instance TypeVar.HasVars Sequent where
  vars (Sequent {hyp = h, concl = c}) =
      Set.union (TypeVar.vars h) (TypeVar.vars c)

-------------------------------------------------------------------------------
-- Type operators
-------------------------------------------------------------------------------

instance TypeOp.HasOps Sequent where
  ops (Sequent {hyp = h, concl = c}) =
      Set.union (TypeOp.ops h) (TypeOp.ops c)

-------------------------------------------------------------------------------
-- Constants
-------------------------------------------------------------------------------

instance Const.HasConsts Sequent where
  consts (Sequent {hyp = h, concl = c}) =
      Set.union (Const.consts h) (Const.consts c)

-------------------------------------------------------------------------------
-- Free variables
-------------------------------------------------------------------------------

instance Var.HasFree Sequent where
  free (Sequent {hyp = h, concl = c}) =
      Set.union (Var.free h) (Var.free c)

-------------------------------------------------------------------------------
-- Substitutions
-------------------------------------------------------------------------------

instance Subst.CanSubst Sequent where
  basicSubst (Sequent {hyp = h, concl = c}) sub =
      (seq',sub'')
    where
      (h',sub') = Subst.basicSubst h sub
      (c',sub'') = Subst.basicSubst c sub'
      seq' = if isNothing h' && isNothing c' then Nothing
             else Just $ Sequent {hyp = fromMaybe h h', concl = fromMaybe c c'}

-------------------------------------------------------------------------------
-- Standard axioms
-------------------------------------------------------------------------------

axiomOfExtensionality :: Sequent
axiomOfExtensionality = mkNullHypUnsafe TermAlpha.axiomOfExtensionality

axiomOfChoice :: Sequent
axiomOfChoice = mkNullHypUnsafe TermAlpha.axiomOfChoice

axiomOfInfinity :: Sequent
axiomOfInfinity = mkNullHypUnsafe  TermAlpha.axiomOfInfinity

standardAxioms :: Set Sequent
standardAxioms =
    Set.fromList
      [axiomOfExtensionality,
       axiomOfChoice,
       axiomOfInfinity]
