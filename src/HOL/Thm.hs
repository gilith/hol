{- |
module: $Header$
description: Higher order logic theorems
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.Thm (
  Thm,
  assume,
  axiomOfChoice,
  axiomOfExtensionality,
  axiomOfInfinity,
  betaConv,
  concl,
  deductAntisym,
  defineConst,
  defineTypeOp,
  dest,
  eqMp,
  hyp,
  mkAbs,
  mkApp,
  refl,
  standardAxioms,
  subst)
where

import Data.Set (Set)
import qualified Data.Set as Set
import HOL.Data
import HOL.Name
import HOL.Sequent (Sequent)
import qualified HOL.Sequent as Sequent
import qualified HOL.Term as Term
import HOL.TermAlpha (TermAlpha)
import qualified HOL.TermAlpha as TermAlpha
import qualified HOL.TypeVar as TypeVar

-------------------------------------------------------------------------------
-- Theorems
-------------------------------------------------------------------------------

newtype Thm = Thm Sequent
  deriving (Eq,Ord,Show)

-------------------------------------------------------------------------------
-- Destructors
-------------------------------------------------------------------------------

dest :: Thm -> Sequent
dest (Thm sq) = sq

hyp :: Thm -> Set TermAlpha
hyp = Sequent.hyp . dest

concl :: Thm -> TermAlpha
concl = Sequent.concl . dest

-------------------------------------------------------------------------------
-- Type variables
-------------------------------------------------------------------------------

instance TypeVar.HasVars Thm where
  vars (Thm sq) = TypeVar.vars sq

-------------------------------------------------------------------------------
-- Standard axioms
-------------------------------------------------------------------------------

standardAxioms :: Set Thm
standardAxioms =
    Set.fromList
      [axiomOfExtensionality,
       axiomOfChoice,
       axiomOfInfinity]

-------------------------------------------------------------------------------
--
-- ------------------------------ axiomOfExtensionality
--   !t : A -> B. (\x. t x) = t
-------------------------------------------------------------------------------

axiomOfExtensionality :: Thm
axiomOfExtensionality = Thm Sequent.axiomOfExtensionality

-------------------------------------------------------------------------------
--
-- -------------------------------------- axiomOfChoice
--   !p (x : A). p x ==> p ((select) p)
-------------------------------------------------------------------------------

axiomOfChoice :: Thm
axiomOfChoice = Thm Sequent.axiomOfChoice

-------------------------------------------------------------------------------
--
-- ------------------------------------------------- axiomOfInfinity
--   ?f : ind -> ind. injective f /\ ~surjective f
-------------------------------------------------------------------------------

axiomOfInfinity :: Thm
axiomOfInfinity = Thm Sequent.axiomOfInfinity

-------------------------------------------------------------------------------
-- Primitive rules of inference
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
--
-- ---------- assume t
--   t |- t
--
-- Side condition: The term t must have boolean type.
-------------------------------------------------------------------------------

assume :: Term -> Maybe Thm
assume tm =
    fmap Thm $ Sequent.mk h c
  where
    c = TermAlpha.mk tm
    h = Set.singleton c

-------------------------------------------------------------------------------
--
-- ------------------------- betaConv ((\v. t) u)
--   |- (\v. t) u = t[u/v]
-------------------------------------------------------------------------------

betaConv :: Term -> Maybe Thm
betaConv tm = do
    (vt,u) <- Term.destApp tm
    (v,t) <- Term.destAbs vt
    undefined v t u

{-
    let
      val (v,t1,t2) =
          case Term.dest t of
            TypeTerm.App' (t',t2) =>
            (case Term.dest t' of
               TypeTerm.Abs' (v,t1) => (v,t1,t2)
             | _ => raise Error "Thm.betaConv: term function not a lambda")
          | _ => raise Error "Thm.betaConv: term not a function application"

      val u =
          if Term.equalVar v t2 then t1
          else
            let
              val tmMap = TermSubst.singletonMap (v,t2)

              val sub = TermSubst.mkMono tmMap
            in
              Option.getOpt (TermSubst.subst sub t1, t1)
            end

      val axioms = emptyAxioms
      and hyp = emptyHyp
      and concl = Term.mkEq (t,u)

      val sequent = Sequent.Sequent {hyp = hyp, concl = concl}
    in
      Thm {axioms = axioms, sequent = sequent}
    end
-}

-------------------------------------------------------------------------------
--         A |- t    B |- u
-- ---------------------------------- deductAntisym
--   (A - {u}) u (B - {t}) |- t = u
-------------------------------------------------------------------------------

deductAntisym :: Thm -> Thm -> Thm
deductAntisym = undefined

-------------------------------------------------------------------------------
--   A |- t = u    B |- t'
-- ------------------------- eqMp
--         A u B |- u
--
-- Side condition: The terms t and t' must be alpha equivalent.
-------------------------------------------------------------------------------

eqMp :: Thm -> Thm -> Thm
eqMp = undefined

-------------------------------------------------------------------------------
--        A |- t = u
-- -------------------------- mkAbs v
--   A |- (\v. t) = (\v. u)
--
-- Side condition: The variable v must not be free in A.
-------------------------------------------------------------------------------

mkAbs :: Var -> Thm -> Thm
mkAbs = undefined

-------------------------------------------------------------------------------
--   A |- f = g    B |- x = y
-- ---------------------------- mkApp
--      A u B |- f x = g y
--
-- Side condition: The types of f and x must be compatible.
-------------------------------------------------------------------------------

mkApp :: Thm -> Thm -> Thm
mkApp = undefined

-------------------------------------------------------------------------------
--
-- ------------ refl t
--   |- t = t
-------------------------------------------------------------------------------

refl :: Term -> Thm
refl = undefined

-------------------------------------------------------------------------------
--          A |- t
-- ------------------------ subst theta
--   A[theta] |- t[theta]
-------------------------------------------------------------------------------

type TermSubst = Integer

subst :: TermSubst -> Thm -> Thm
subst = undefined

-------------------------------------------------------------------------------
-- Principles of definition
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
--
-- --------------- defineConst name t
--   |- name = t
--
-- where name is a new constant with the same type as the term t.
--
-- Side condition: The term t has no free variables.
-- Side condition: All type variables in t also appear in the type of t.
-------------------------------------------------------------------------------

defineConst :: Name -> Term -> (Const,Thm)
defineConst = undefined

-------------------------------------------------------------------------------
--             |- p t
-- ----------------------------------- defineTypeOp name abs rep tyVars
--   |- (\a. abs (rep a)) = (\a. a)
--   |- (\r. rep (abs r) = r) = (\r. p r)
--
-- where if p has type 'a -> bool, then abs and rep are new constants with
-- types 'a -> ty and ty -> 'a, respectively.
--
-- Side condition: tyVars lists all the type variables in p precisely once.
-------------------------------------------------------------------------------

defineTypeOp :: Name -> Name -> Name -> [Name] -> Thm ->
                (TypeOp,Const,Const,Thm,Thm)
defineTypeOp = undefined
