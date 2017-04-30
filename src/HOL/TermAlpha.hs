{- |
module: $Header$
description: Higher order logic terms modulo alpha-equivalence
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.TermAlpha
where

import Data.Set (Set)
import qualified Data.Set as Set
import HOL.Data
import HOL.Name
import qualified HOL.Subst as Subst
import qualified HOL.Term as Term
import qualified HOL.Type as Type
import qualified HOL.TypeVar as TypeVar
import qualified HOL.Var as Var

-------------------------------------------------------------------------------
-- Terms modulo alpha-equivalence
-------------------------------------------------------------------------------

newtype TermAlpha = TermAlpha Term
  deriving Show

instance Eq TermAlpha where
  (TermAlpha tm1) == (TermAlpha tm2) = Term.alphaEqual tm1 tm2

instance Ord TermAlpha where
  compare (TermAlpha tm1) (TermAlpha tm2) = Term.alphaCompare tm1 tm2

-------------------------------------------------------------------------------
-- Constructors and destructors
-------------------------------------------------------------------------------

mk :: Term -> TermAlpha
mk = TermAlpha

dest :: TermAlpha -> Term
dest (TermAlpha tm) = tm

-------------------------------------------------------------------------------
-- Type
-------------------------------------------------------------------------------

typeOf :: TermAlpha -> Type
typeOf = Term.typeOf . dest

isBool :: TermAlpha -> Bool
isBool = Type.isBool . typeOf

-------------------------------------------------------------------------------
-- Type variables
-------------------------------------------------------------------------------

instance TypeVar.HasVars TermAlpha where
  vars (TermAlpha tm) = TypeVar.vars tm

-------------------------------------------------------------------------------
-- Free variables
-------------------------------------------------------------------------------

instance Var.HasFree TermAlpha where
  free (TermAlpha tm) = Var.free tm

-------------------------------------------------------------------------------
-- Substitutions
-------------------------------------------------------------------------------

instance Subst.CanSubst TermAlpha where
  basicSubst (TermAlpha tm) sub =
      (atm',sub')
    where
      (tm',sub') = Subst.basicSubst tm sub
      atm' = fmap TermAlpha tm'

-------------------------------------------------------------------------------
-- Standard axioms
-------------------------------------------------------------------------------

axiomOfExtensionality :: TermAlpha
axiomOfExtensionality =
    case axiom of
      Just tm -> mk tm
      Nothing -> error "HOL.TermAlpha.axiomOfExtensionality"
  where
    axiom = do
        let ty0 = Type.alpha
        let ty1 = Type.beta
        let ty2 = Type.mkFun ty0 ty1
        let ty3 = Type.bool
        let ty4 = Type.mkFun ty2 ty3
        let v0 = Var.mk (mkGlobal "a") ty4
        let v1 = Var.mk (mkGlobal "b") ty2
        let v2 = Var.mk (mkGlobal "c") ty3
        let v3 = Var.mk (mkGlobal "d") ty2
        let v4 = Var.mk (mkGlobal "e") ty0
        let tm0 = Term.mkVar v0
        let tm1 = Term.mkVar v2
        let tm2 = Term.mkAbs v2 tm1
        let tm3 = Term.mkRefl tm2
        let tm4 = Term.mkAbs v1 tm3
        tm5 <- Term.mkEq tm0 tm4
        let tm6 = Term.mkAbs v0 tm5
        let tm7 = Term.mkVar v3
        let tm8 = Term.mkVar v4
        tm9 <- Term.mkApp tm7 tm8
        let tm10 = Term.mkAbs v4 tm9
        tm11 <- Term.mkEq tm10 tm7
        let tm12 = Term.mkAbs v3 tm11
        tm13 <- Term.mkApp tm6 tm12
        return tm13

axiomOfChoice :: TermAlpha
axiomOfChoice =
    case axiom of
      Just tm -> mk tm
      Nothing -> error "HOL.TermAlpha.axiomOfChoice"
  where
    axiom = do
        let ty0 = Type.alpha
        let ty1 = Type.bool
        let ty2 = Type.mkFun ty0 ty1
        let ty3 = Type.mkFun ty2 ty1
        let ty4 = Type.mkFun ty1 ty1
        let ty5 = Type.mkFun ty1 ty4
        let v0 = Var.mk (mkGlobal "a") ty3
        let v1 = Var.mk (mkGlobal "b") ty2
        let v2 = Var.mk (mkGlobal "c") ty1
        let v3 = Var.mk (mkGlobal "d") ty2
        let v4 = Var.mk (mkGlobal "e") ty2
        let v5 = Var.mk (mkGlobal "f") ty0
        let v6 = Var.mk (mkGlobal "g") ty0
        let v7 = Var.mk (mkGlobal "h") ty1
        let v8 = Var.mk (mkGlobal "i") ty1
        let v9 = Var.mk (mkGlobal "j") ty1
        let v10 = Var.mk (mkGlobal "k") ty1
        let v11 = Var.mk (mkGlobal "l") ty5
        let v12 = Var.mk (mkGlobal "m") ty5
        let tm0 = Term.mkVar v0
        let tm1 = Term.mkVar v2
        let tm2 = Term.mkAbs v2 tm1
        let tm3 = Term.mkRefl tm2
        let tm4 = Term.mkAbs v1 tm3
        tm5 <- Term.mkEq tm0 tm4
        let tm6 = Term.mkAbs v0 tm5
        let tm7 = Term.mkVar v4
        let tm8 = Term.mkAbs v5 tm3
        tm9 <- Term.mkEq tm7 tm8
        let tm10 = Term.mkAbs v4 tm9
        let tm11 = Term.mkVar v11
        let tm12 = Term.mkVar v9
        tm13 <- Term.mkApp tm11 tm12
        let tm14 = Term.mkVar v10
        tm15 <- Term.mkApp tm13 tm14
        let tm16 = Term.mkAbs v11 tm15
        let tm17 = Term.mkVar v12
        tm18 <- Term.mkApp tm17 tm3
        tm19 <- Term.mkApp tm18 tm3
        let tm20 = Term.mkAbs v12 tm19
        tm21 <- Term.mkEq tm16 tm20
        let tm22 = Term.mkAbs v10 tm21
        let tm23 = Term.mkAbs v9 tm22
        let tm24 = Term.mkVar v7
        tm25 <- Term.mkApp tm23 tm24
        let tm26 = Term.mkVar v8
        tm27 <- Term.mkApp tm25 tm26
        tm28 <- Term.mkEq tm27 tm24
        let tm29 = Term.mkAbs v8 tm28
        let tm30 = Term.mkAbs v7 tm29
        let tm31 = Term.mkVar v3
        let tm32 = Term.mkVar v6
        tm33 <- Term.mkApp tm31 tm32
        tm34 <- Term.mkApp tm30 tm33
        let tm35 = Term.mkSelectConst ty0
        tm36 <- Term.mkApp tm35 tm31
        tm37 <- Term.mkApp tm31 tm36
        tm38 <- Term.mkApp tm34 tm37
        let tm39 = Term.mkAbs v6 tm38
        tm40 <- Term.mkApp tm10 tm39
        let tm41 = Term.mkAbs v3 tm40
        tm42 <- Term.mkApp tm6 tm41
        return tm42

axiomOfInfinity :: TermAlpha
axiomOfInfinity =
    case axiom of
      Just tm -> mk tm
      Nothing -> error "HOL.TermAlpha.axiomOfInfinity"
  where
    axiom = do
        let ty0 = Type.ind
        let ty1 = Type.mkFun ty0 ty0
        let ty2 = Type.bool
        let ty3 = Type.mkFun ty1 ty2
        let ty4 = Type.mkFun ty2 ty2
        let ty5 = Type.mkFun ty2 ty4
        let ty6 = Type.mkFun ty0 ty2
        let v0 = Var.mk (mkGlobal "a") ty3
        let v1 = Var.mk (mkGlobal "b") ty4
        let v2 = Var.mk (mkGlobal "c") ty2
        let v3 = Var.mk (mkGlobal "d") ty2
        let v4 = Var.mk (mkGlobal "e") ty2
        let v5 = Var.mk (mkGlobal "f") ty2
        let v6 = Var.mk (mkGlobal "g") ty2
        let v7 = Var.mk (mkGlobal "h") ty2
        let v8 = Var.mk (mkGlobal "i") ty2
        let v9 = Var.mk (mkGlobal "j") ty5
        let v10 = Var.mk (mkGlobal "k") ty5
        let v11 = Var.mk (mkGlobal "l") ty3
        let v12 = Var.mk (mkGlobal "m") ty1
        let v13 = Var.mk (mkGlobal "n") ty1
        let v14 = Var.mk (mkGlobal "p") ty1
        let v15 = Var.mk (mkGlobal "q") ty6
        let v16 = Var.mk (mkGlobal "r") ty0
        let v17 = Var.mk (mkGlobal "s") ty0
        let v18 = Var.mk (mkGlobal "t") ty0
        let v19 = Var.mk (mkGlobal "u") ty2
        let v20 = Var.mk (mkGlobal "v") ty0
        let v21 = Var.mk (mkGlobal "w") ty6
        let v22 = Var.mk (mkGlobal "x") ty2
        let v23 = Var.mk (mkGlobal "y") ty0
        let v24 = Var.mk (mkGlobal "z") ty0
        let tm0 = Term.mkVar v1
        let tm1 = Term.mkVar v3
        let tm2 = Term.mkAbs v3 tm1
        let tm3 = Term.mkRefl tm2
        let tm4 = Term.mkAbs v2 tm3
        tm5 <- Term.mkEq tm0 tm4
        let tm6 = Term.mkAbs v1 tm5
        let tm7 = Term.mkVar v9
        let tm8 = Term.mkVar v7
        tm9 <- Term.mkApp tm7 tm8
        let tm10 = Term.mkVar v8
        tm11 <- Term.mkApp tm9 tm10
        let tm12 = Term.mkAbs v9 tm11
        let tm13 = Term.mkVar v10
        tm14 <- Term.mkApp tm13 tm3
        tm15 <- Term.mkApp tm14 tm3
        let tm16 = Term.mkAbs v10 tm15
        tm17 <- Term.mkEq tm12 tm16
        let tm18 = Term.mkAbs v8 tm17
        let tm19 = Term.mkAbs v7 tm18
        let tm20 = Term.mkVar v5
        tm21 <- Term.mkApp tm19 tm20
        let tm22 = Term.mkVar v6
        tm23 <- Term.mkApp tm21 tm22
        tm24 <- Term.mkEq tm23 tm20
        let tm25 = Term.mkAbs v6 tm24
        let tm26 = Term.mkAbs v5 tm25
        let tm27 = Term.mkVar v11
        let tm28 = Term.mkAbs v12 tm3
        tm29 <- Term.mkEq tm27 tm28
        let tm30 = Term.mkAbs v11 tm29
        let tm31 = Term.mkVar v0
        let tm32 = Term.mkVar v13
        tm33 <- Term.mkApp tm31 tm32
        tm34 <- Term.mkApp tm26 tm33
        let tm35 = Term.mkVar v4
        tm36 <- Term.mkApp tm34 tm35
        let tm37 = Term.mkAbs v13 tm36
        tm38 <- Term.mkApp tm30 tm37
        tm39 <- Term.mkApp tm26 tm38
        tm40 <- Term.mkApp tm39 tm35
        let tm41 = Term.mkAbs v4 tm40
        tm42 <- Term.mkApp tm6 tm41
        let tm43 = Term.mkAbs v0 tm42
        let tm44 = Term.mkVar v15
        let tm45 = Term.mkAbs v16 tm3
        tm46 <- Term.mkEq tm44 tm45
        let tm47 = Term.mkAbs v15 tm46
        let tm48 = Term.mkVar v14
        let tm49 = Term.mkVar v17
        tm50 <- Term.mkApp tm48 tm49
        let tm51 = Term.mkVar v18
        tm52 <- Term.mkApp tm48 tm51
        tm53 <- Term.mkEq tm50 tm52
        tm54 <- Term.mkApp tm26 tm53
        tm55 <- Term.mkEq tm49 tm51
        tm56 <- Term.mkApp tm54 tm55
        let tm57 = Term.mkAbs v18 tm56
        tm58 <- Term.mkApp tm47 tm57
        let tm59 = Term.mkAbs v17 tm58
        tm60 <- Term.mkApp tm47 tm59
        tm61 <- Term.mkApp tm19 tm60
        let tm62 = Term.mkVar v19
        tm63 <- Term.mkApp tm26 tm62
        tm64 <- Term.mkApp tm6 tm2
        tm65 <- Term.mkApp tm63 tm64
        let tm66 = Term.mkAbs v19 tm65
        let tm67 = Term.mkVar v21
        let tm68 = Term.mkVar v23
        tm69 <- Term.mkApp tm67 tm68
        tm70 <- Term.mkApp tm26 tm69
        let tm71 = Term.mkVar v22
        tm72 <- Term.mkApp tm70 tm71
        let tm73 = Term.mkAbs v23 tm72
        tm74 <- Term.mkApp tm47 tm73
        tm75 <- Term.mkApp tm26 tm74
        tm76 <- Term.mkApp tm75 tm71
        let tm77 = Term.mkAbs v22 tm76
        tm78 <- Term.mkApp tm6 tm77
        let tm79 = Term.mkAbs v21 tm78
        let tm80 = Term.mkVar v20
        let tm81 = Term.mkVar v24
        tm82 <- Term.mkApp tm48 tm81
        tm83 <- Term.mkEq tm80 tm82
        let tm84 = Term.mkAbs v24 tm83
        tm85 <- Term.mkApp tm79 tm84
        let tm86 = Term.mkAbs v20 tm85
        tm87 <- Term.mkApp tm47 tm86
        tm88 <- Term.mkApp tm66 tm87
        tm89 <- Term.mkApp tm61 tm88
        let tm90 = Term.mkAbs v14 tm89
        tm91 <- Term.mkApp tm43 tm90
        return tm91

standardAxioms :: Set TermAlpha
standardAxioms =
    Set.fromList
      [axiomOfExtensionality,
       axiomOfChoice,
       axiomOfInfinity]

standardAxiomName :: TermAlpha -> String
standardAxiomName tm =
     if tm == axiomOfExtensionality then "AXIOM OF EXTENSIONALITY"
     else if tm == axiomOfChoice then "AXIOM OF CHOICE"
     else if tm == axiomOfInfinity then "AXIOM OF INFINITY"
     else error "HOL.TermAlpha.standardAxiomName: not a standard axiom"
