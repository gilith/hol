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
import HOL.Util (mkUnsafe2)
import qualified HOL.Var as Var

-------------------------------------------------------------------------------
-- Applying equalities at subterms
-------------------------------------------------------------------------------

rator :: Thm -> Term -> Maybe Thm
rator th tm = Thm.mkApp th (Thm.refl tm)

ratorUnsafe :: Thm -> Term -> Thm
ratorUnsafe = mkUnsafe2 "HOL.Rule.rator" rator

rand :: Term -> Thm -> Maybe Thm
rand tm th = Thm.mkApp (Thm.refl tm) th

randUnsafe :: Term -> Thm -> Thm
randUnsafe = mkUnsafe2 "HOL.Rule.rand" rand

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

transUnsafe :: Thm -> Thm -> Thm
transUnsafe = mkUnsafe2 "HOL.Rule.trans" trans

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

alphaSequent :: Sequent -> Thm -> Maybe Thm
alphaSequent sq th = do
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
    let sub = Subst.fromListUnsafe [] vcs
    def <- foldM (flip proveHyp) (Thm.subst sub th) defs
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

-------------------------------------------------------------------------------
-- The legacy (a.k.a. HOL Light) version of defineTypeOp
-------------------------------------------------------------------------------

defineTypeOpLegacy :: Name -> Name -> Name -> [TypeVar] -> Thm ->
                      Maybe (TypeOp,Const,Const,Thm,Thm)
defineTypeOpLegacy opName absName repName tyVarl existenceTh = do
    (opT,absC,repC,absRepTh,repAbsTh) <-
      Thm.defineTypeOp opName absName repName tyVarl existenceTh
    let absRepTh' = unsafe convertAbsRep absRepTh
    let repAbsTh' = unsafe convertRepAbs repAbsTh
    return (opT,absC,repC,absRepTh',repAbsTh')
  where
    unsafe convert th =
        case convert th of
          Just th' -> th'
          Nothing -> error "HOL.Rule.defineTypeOpLegacy failed"

    convertAbsRep th0 = do  -- ⊢ (\a. abs (rep a)) = (\a. a)
        aId <- Term.rhs $ TermAlpha.dest $ Thm.concl th0  -- \a. a
        (_,aTm) <- Term.destAbs aId  -- a
        th1 <- rator th0 aTm  -- ⊢ (\a. abs (rep a)) a = (\a. a) a
        (tm0,rhsTm) <- Term.destApp $ TermAlpha.dest $ Thm.concl th1
        (eqTm,lhsTm) <- Term.destApp tm0
        th2 <- Thm.betaConv lhsTm  -- ⊢ (\a. abs (rep a)) a = abs (rep a)
        th3 <- rand eqTm th2
        th4 <- Thm.betaConv rhsTm  -- ⊢ (\a. a) a = a
        th5 <- Thm.mkApp th3 th4
        Thm.eqMp th5 th1  -- ⊢ abs (rep a) = a

    convertRepAbs th0 = do  -- (\r. rep (abs r) = r) = (\r. p r)
        tm0 <- Term.lhs $ TermAlpha.dest $ Thm.concl th0
        (_,tm1) <- Term.destAbs tm0  -- rep (abs r) = r
        rTm <- Term.rhs tm1  -- r
        th1 <- rator th0 rTm  -- ⊢ (\r. rep (abs r) = r) r <=> (\r. p r) r
        (tm2,rhsTm) <- Term.destApp $ TermAlpha.dest $ Thm.concl th1
        (iffTm,lhsTm) <- Term.destApp tm2
        th2 <- Thm.betaConv lhsTm
        th3 <- rand iffTm th2
        th4 <- Thm.betaConv rhsTm
        th5 <- Thm.mkApp th3 th4
        th6 <- Thm.eqMp th5 th1  -- ⊢ rep (abs r) = r <=> p r
        sym th6  -- ⊢ p r <=> rep (abs r) = r
