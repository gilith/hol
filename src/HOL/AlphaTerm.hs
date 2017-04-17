{- |
module: $Header$
description: Higher order logic terms modulo alpha-equivalence
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.AlphaTerm
where

import Data.Set (Set)
import qualified Data.Set as Set
import HOL.Data
import qualified HOL.Term as Term
import qualified HOL.Type as Type

-------------------------------------------------------------------------------
-- Terms modulo alpha-equivalence
-------------------------------------------------------------------------------

newtype AlphaTerm = AlphaTerm Term
  deriving Show

instance Eq AlphaTerm where
  (AlphaTerm tm1) == (AlphaTerm tm2) = Term.alphaEqual tm1 tm2

instance Ord AlphaTerm where
  compare (AlphaTerm tm1) (AlphaTerm tm2) = Term.alphaCompare tm1 tm2

-------------------------------------------------------------------------------
-- Constructors and destructors
-------------------------------------------------------------------------------

mk :: Term -> AlphaTerm
mk = AlphaTerm

dest :: AlphaTerm -> Term
dest (AlphaTerm tm) = tm

-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

typeOf :: AlphaTerm -> Type
typeOf = Term.typeOf . dest

isBool :: AlphaTerm -> Bool
isBool = Type.isBool . typeOf

-------------------------------------------------------------------------------
-- Standard axioms
-------------------------------------------------------------------------------

axiomOfExtensionality :: AlphaTerm
axiomOfExtensionality = mk Term.axiomOfExtensionality

axiomOfChoice :: AlphaTerm
axiomOfChoice = mk Term.axiomOfChoice

axiomOfInfinity :: AlphaTerm
axiomOfInfinity = mk Term.axiomOfInfinity

standardAxioms :: Set AlphaTerm
standardAxioms =
    Set.fromList
      [axiomOfExtensionality,
       axiomOfChoice,
       axiomOfInfinity]

standardAxiomName :: AlphaTerm -> String
standardAxiomName tm =
     if tm == axiomOfExtensionality then "AXIOM OF EXTENSIONALITY"
     else if tm == axiomOfChoice then "AXIOM OF CHOICE"
     else if tm == axiomOfInfinity then "AXIOM OF INFINITY"
     else error "not a standard axiom"
