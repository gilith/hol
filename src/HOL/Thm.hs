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
  nullHyp,
  refl,
  standardAxioms,
  subst)
where

import Control.Monad (guard)
import Data.Set (Set)
import qualified Data.Set as Set
import HOL.Data
import HOL.Name
import HOL.Sequent (Sequent)
import qualified HOL.Sequent as Sequent
import HOL.Subst (Subst)
import qualified HOL.Subst as Subst
import qualified HOL.Term as Term
import HOL.TermAlpha (TermAlpha)
import qualified HOL.TermAlpha as TermAlpha
import qualified HOL.Type as Type
import qualified HOL.TypeVar as TypeVar
import qualified HOL.Var as Var

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

nullHyp :: Thm -> Bool
nullHyp = Sequent.nullHyp . dest

-------------------------------------------------------------------------------
-- Type variables
-------------------------------------------------------------------------------

instance TypeVar.HasVars Thm where
  vars (Thm sq) = TypeVar.vars sq

-------------------------------------------------------------------------------
-- Free variables
-------------------------------------------------------------------------------

instance Var.HasFree Thm where
  free (Thm sq) = Var.free sq

-------------------------------------------------------------------------------
-- Substitutions
-------------------------------------------------------------------------------

instance Subst.CanSubst Thm where
  basicSubst th sub =
      (th',sub')
    where
      Thm sq = th
      (sq',sub') = Subst.basicSubst sq sub
      th' = fmap Thm sq'

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
    let tm' = Subst.trySubst (Subst.singleton v u) t
    let sq = Sequent.mkNullHypUnsafe $ TermAlpha.mk $ Term.mkEqUnsafe tm tm'
    return $ Thm sq

-------------------------------------------------------------------------------
--         A |- t        B |- u
-- -------------------------------------- deductAntisym
--   (A - {u}) union (B - {t}) |- t = u
-------------------------------------------------------------------------------

deductAntisym :: Thm -> Thm -> Thm
deductAntisym (Thm sq1) (Thm sq2) =
    Thm $ Sequent.mkUnsafe h c
  where
    (h1,c1) = Sequent.dest sq1
    (h2,c2) = Sequent.dest sq2
    h = Set.union (Set.delete c2 h1) (Set.delete c1 h2)
    c = TermAlpha.mk $ Term.mkEqUnsafe (TermAlpha.dest c1) (TermAlpha.dest c2)

-------------------------------------------------------------------------------
--   A |- t = u    B |- t'
-- ------------------------- eqMp
--       A union B |- u
--
-- Side condition: The terms t and t' must be alpha equivalent.
-------------------------------------------------------------------------------

eqMp :: Thm -> Thm -> Maybe Thm
eqMp (Thm sq1) (Thm sq2) = do
    (t,u) <- Term.destEq $ TermAlpha.dest c1
    guard (TermAlpha.mk t == c2)
    let c = TermAlpha.mk u
    return $ Thm $ Sequent.mkUnsafe h c
  where
    (h1,c1) = Sequent.dest sq1
    (h2,c2) = Sequent.dest sq2
    h = Set.union h1 h2

-------------------------------------------------------------------------------
--        A |- t = u
-- -------------------------- mkAbs v
--   A |- (\v. t) = (\v. u)
--
-- Side condition: The variable v must not be free in A.
-------------------------------------------------------------------------------

mkAbs :: Var -> Thm -> Maybe Thm
mkAbs v (Thm sq) = do
    guard (Var.notFreeIn v h)
    (t,u) <- Term.destEq $ TermAlpha.dest tu
    let vt = Term.mkAbs v t
    let vu = Term.mkAbs v u
    let c = TermAlpha.mk $ Term.mkEqUnsafe vt vu
    return $ Thm $ Sequent.mkUnsafe h c
  where
    (h,tu) = Sequent.dest sq

-------------------------------------------------------------------------------
--   A |- f = g    B |- x = y
-- ---------------------------- mkApp
--    A union B |- f x = g y
--
-- Side condition: The types of f and x must be compatible.
-------------------------------------------------------------------------------

mkApp :: Thm -> Thm -> Maybe Thm
mkApp (Thm sq1) (Thm sq2) = do
    (f,g) <- Term.destEq $ TermAlpha.dest c1
    (x,y) <- Term.destEq $ TermAlpha.dest c2
    fx <- Term.mkApp f x
    gy <- Term.mkApp g y
    let c = TermAlpha.mk $ Term.mkEqUnsafe fx gy
    return $ Thm $ Sequent.mkUnsafe h c
  where
    (h1,c1) = Sequent.dest sq1
    (h2,c2) = Sequent.dest sq2
    h = Set.union h1 h2

-------------------------------------------------------------------------------
--
-- ------------ refl t
--   |- t = t
-------------------------------------------------------------------------------

refl :: Term -> Thm
refl = Thm . Sequent.mkNullHypUnsafe .TermAlpha.mk . Term.mkRefl

-------------------------------------------------------------------------------
--          A |- t
-- ------------------------ subst theta
--   A[theta] |- t[theta]
-------------------------------------------------------------------------------

subst :: Subst -> Thm -> Thm
subst = Subst.trySubst

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

defineConst :: Name -> Term -> Maybe (Const,Thm)
defineConst name t = do
    guard (Var.closed t)
    guard (Set.isSubsetOf (TypeVar.vars t) (TypeVar.vars ty))
    return (nameC, Thm $ Sequent.mkNullHypUnsafe c)
  where
    nameC = Const name (DefConstProv (ConstDef t))
    ty = Term.typeOf t
    c = TermAlpha.mk $ Term.mkEqUnsafe (Term.mkConst nameC ty) t

-------------------------------------------------------------------------------
--             |- p t
-- ---------------------------------------- defineTypeOp name abs rep tyVars
--   |- (\a. abs (rep a)) = (\a. a)
--   |- (\r. rep (abs r) = r) = (\r. p r)
--
-- where if p has type r -> bool, then abs and rep are new constants with
-- types r -> a and a -> r, respectively, where a is the new type
-- tyVars name.
--
-- Side condition: tyVars lists all the type variables in p precisely once.
-------------------------------------------------------------------------------

defineTypeOp :: Name -> Name -> Name -> [TypeVar] -> Thm ->
                Maybe (TypeOp,Const,Const,Thm,Thm)
defineTypeOp opName absName repName tyVarl existenceTh = do
    guard (length tyVarl == Set.size tyVars)
    guard (nullHyp existenceTh)
    (p,witness) <- Term.destApp $ TermAlpha.dest $ concl existenceTh
    guard (Var.closed p)
    guard (TypeVar.vars p == tyVars)
    let def = TypeOpDef p tyVarl
    let opT = TypeOp opName $ DefTypeOpProv def
    let absC = Const absName $ AbsConstProv def
    let repC = Const repName $ RepConstProv def
    let aTy = Type.mkOp opT $ map Type.mkVar tyVarl
    let rTy = Term.typeOf witness
    let absTm = Term.mkConst absC $ Type.mkFun rTy aTy
    let repTm = Term.mkConst repC $ Type.mkFun aTy rTy
    let absRepTh =
            Thm $ Sequent.mkNullHypUnsafe $ TermAlpha.mk c
          where
            aVar = Var (mkGlobal "a") aTy
            aTm = Term.mkVar aVar
            l = Term.mkAppUnsafe absTm $ Term.mkAppUnsafe repTm aTm
            r = aTm
            c = Term.mkEqUnsafe (Term.mkAbs aVar l) (Term.mkAbs aVar r)
    let repAbsTh =
            Thm $ Sequent.mkNullHypUnsafe $ TermAlpha.mk c
          where
            rVar = Var (mkGlobal "r") rTy
            rTm = Term.mkVar rVar
            ll = Term.mkAppUnsafe repTm $ Term.mkAppUnsafe absTm rTm
            l = Term.mkEqUnsafe ll rTm
            r = Term.mkAppUnsafe p rTm
            c = Term.mkEqUnsafe (Term.mkAbs rVar l) (Term.mkAbs rVar r)
    return (opT,absC,repC,absRepTh,repAbsTh)
  where
    tyVars = Set.fromList tyVarl
