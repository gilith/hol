{- |
module: $Header$
description: Higher order logic derived rules of inference
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.Rule
where

import Control.Monad (foldM,guard)
import qualified Data.Map as Map
import qualified Data.Set as Set
import HOL.Data
import HOL.Name
import HOL.Sequent (Sequent)
import qualified HOL.Sequent as Sequent
import qualified HOL.Subst as Subst
import qualified HOL.Term as Term
import qualified HOL.TermAlpha as TermAlpha
import HOL.Thm (Thm)
import qualified HOL.Thm as Thm
import qualified HOL.Var as Var

-------------------------------------------------------------------------------
-- Applying equalities at subterms
-------------------------------------------------------------------------------

rator :: Thm -> Term -> Maybe Thm
rator th tm = Thm.mkApp th (Thm.refl tm)

rand :: Term -> Thm -> Maybe Thm
rand tm th = Thm.mkApp (Thm.refl tm) th

-------------------------------------------------------------------------------
-- Symmetry of equality
-------------------------------------------------------------------------------

sym :: Thm -> Maybe Thm
sym th = do
    el <- Term.rator $ TermAlpha.dest $ Thm.concl th
    (e,l) <- Term.destApp el
    let th0 = Thm.refl l
    th1 <- rand e th
    th2 <- Thm.mkApp th1 th0
    Thm.eqMp th2 th0

-------------------------------------------------------------------------------
-- Transitivity of equality
-------------------------------------------------------------------------------

trans :: Thm -> Thm -> Maybe Thm
trans th1 th2 = do
    tm <- Term.rator $ TermAlpha.dest $ Thm.concl th1
    th3 <- rand tm th2
    Thm.eqMp th3 th1

-------------------------------------------------------------------------------
-- Proving hypotheses
-------------------------------------------------------------------------------

proveHyp :: Thm -> Thm -> Maybe Thm
proveHyp th1 th2 = do
    let th3 = Thm.deductAntisym th1 th2
    Thm.eqMp th3 th1

-------------------------------------------------------------------------------
-- Alpha conversion
-------------------------------------------------------------------------------

alpha :: Term -> Thm -> Maybe Thm
alpha c th =
    if TermAlpha.dest (Thm.concl th) == c then Just th
    else Thm.eqMp (Thm.refl c) th

alphaHyp :: Term -> Thm -> Maybe Thm
alphaHyp h th =
    case Set.lookupLE ha (Thm.hyp th) of
      Nothing -> Nothing
      Just ha' ->
        if ha' /= ha then Nothing
        else if TermAlpha.dest ha' == h then Just th
        else do
          th0 <- Thm.assume h
          proveHyp th0 th
  where
    ha = TermAlpha.mk h

alphaSeq :: Sequent -> Thm -> Maybe Thm
alphaSeq sq th = do
    th0 <- alpha (TermAlpha.dest c) th
    guard (Thm.hyp th == h)
    foldM (flip alphaHyp) th0 hl
  where
    (h,c) = Sequent.dest sq
    hl = map TermAlpha.dest $ Set.toList h

-------------------------------------------------------------------------------
-- The new principle of constant definition
-------------------------------------------------------------------------------

defineConstList :: [(Name,Var)] -> Thm -> Maybe ([Const],Thm)
defineConstList nvs th = do
    vm <- foldM addVar Map.empty $ Set.toList $ Thm.hyp th
    guard (Set.isSubsetOf (Var.free (Thm.concl th)) (Map.keysSet vm))
    (cs,vcs,defs,vm0) <- foldM delVar ([],[],[],vm) nvs
    guard (Map.null vm0)
    let sub = Subst.fromList [] vcs
    def <- foldM proveHyp (Thm.subst sub th) defs
    return (cs,def)
  where
    addVar vm h = do
      (vt,tm) <- Term.destEq $ TermAlpha.dest h
      v <- Term.destVar vt
      guard (Map.notMember v vm)
      return $ Map.insert v tm vm

    delVar (cs,vcs,defs,vm) (n,v) = do
      tm <- Map.lookup v vm
      (c,def) <- Thm.defineConst n tm
      let vc = (v, Term.mkConst c (Var.typeOf v))
      return (c : cs, vc : vcs, def : defs, Map.delete v vm)
