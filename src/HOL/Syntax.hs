{- |
module: $Header$
description: Higher order logic syntax
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.Syntax
where

import qualified HOL.Const as Const
import HOL.Data (Const,Term,Type,Var)
--import HOL.Name (Name)
--import qualified HOL.Name as Name
--import HOL.Print (toString)
--import HOL.Term (renameFresh)
import qualified HOL.Term as Term
import HOL.Theory (Theory)
import qualified HOL.Theory as Theory
import qualified HOL.Type as Type
--import qualified HOL.TypeOp as TypeOp
import HOL.Util (mkUnsafe1,mkUnsafe2,mkUnsafe3)
import qualified HOL.Var as Var

-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

mkUnaryType :: Type -> Type
mkUnaryType a = Type.mkFun a a

mkBinaryType :: Type -> Type
mkBinaryType a = Type.mkFun a (mkUnaryType a)

-------------------------------------------------------------------------------
-- Constants
-------------------------------------------------------------------------------

existsConst :: Theory -> Maybe Const
existsConst thy = Theory.lookupConst thy Const.existsName

forallConst :: Theory -> Maybe Const
forallConst thy = Theory.lookupConst thy Const.forallName

-------------------------------------------------------------------------------
-- Booleans
-------------------------------------------------------------------------------

-- Types

mkQuantType :: Type -> Type
mkQuantType a = Type.mkFun (Type.mkFun a Type.bool) Type.bool

-- Truth

trueConst :: Theory -> Maybe Const
trueConst thy = Theory.lookupConst thy Const.trueName

trueTerm :: Theory -> Maybe Term
trueTerm thy = do
    c <- trueConst thy
    return $ Term.mkConst c Type.bool

trueTermUnsafe :: Theory -> Term
trueTermUnsafe = mkUnsafe1 "HOL.Syntax.trueTerm" trueTerm

-- Falsity

falseConst :: Theory -> Maybe Const
falseConst thy = Theory.lookupConst thy Const.falseName

falseTerm :: Theory -> Maybe Term
falseTerm thy = do
    c <- falseConst thy
    return $ Term.mkConst c Type.bool

falseTermUnsafe :: Theory -> Term
falseTermUnsafe = mkUnsafe1 "HOL.Syntax.falseTerm" falseTerm

-- Negation

negConst :: Theory -> Maybe Const
negConst thy = Theory.lookupConst thy Const.negName

negTerm :: Theory -> Maybe Term
negTerm thy = do
  c <- negConst thy
  return $ Term.mkConst c (mkUnaryType Type.bool)

mkNegTerm :: Theory -> Term -> Maybe Term
mkNegTerm thy t = do
  c <- negTerm thy
  Term.mkApp c t

mkNegTermUnsafe :: Theory -> Term -> Term
mkNegTermUnsafe = mkUnsafe2 "HOL.Syntax.mkNegTerm" mkNegTerm

-- Implication

impConst :: Theory -> Maybe Const
impConst thy = Theory.lookupConst thy Const.impName

impTerm :: Theory -> Maybe Term
impTerm thy = do
  c <- impConst thy
  return $ Term.mkConst c (mkBinaryType Type.bool)

mkImpTerm :: Theory -> Term -> Term -> Maybe Term
mkImpTerm thy t u = do
  c <- impTerm thy
  Term.listMkApp c [t,u]

mkImpTermUnsafe :: Theory -> Term -> Term -> Term
mkImpTermUnsafe = mkUnsafe3 "HOL.Syntax.mkImpTerm" mkImpTerm

-- Existential quantification

existsTerm :: Theory -> Type -> Maybe Term
existsTerm thy a = do
  c <- existsConst thy
  return $ Term.mkConst c (mkQuantType a)

mkExistsTerm :: Theory -> Var -> Term -> Maybe Term
mkExistsTerm thy v t = do
  q <- existsTerm thy (Var.typeOf v)
  Term.mkApp q (Term.mkAbs v t)

mkExistsTermUnsafe :: Theory -> Var -> Term -> Term
mkExistsTermUnsafe = mkUnsafe3 "HOL.Syntax.mkExistsTerm" mkExistsTerm

listMkExistsTerm :: Theory -> [Var] -> Term -> Maybe Term
listMkExistsTerm _ [] t = return t
listMkExistsTerm thy (v : vs) t = do
  u <- listMkExistsTerm thy vs t
  mkExistsTerm thy v u

listMkExistsTermUnsafe :: Theory -> [Var] -> Term -> Term
listMkExistsTermUnsafe = mkUnsafe3 "HOL.Syntax.listMkExistsTerm" listMkExistsTerm

-- Universal quantification

forallTerm :: Theory -> Type -> Maybe Term
forallTerm thy a = do
  c <- forallConst thy
  return $ Term.mkConst c (mkQuantType a)

mkForallTerm :: Theory -> Var -> Term -> Maybe Term
mkForallTerm thy v t = do
  q <- forallTerm thy (Var.typeOf v)
  Term.mkApp q (Term.mkAbs v t)

mkForallTermUnsafe :: Theory -> Var -> Term -> Term
mkForallTermUnsafe = mkUnsafe3 "HOL.Syntax.mkForallTerm" mkForallTerm

listMkForallTerm :: Theory -> [Var] -> Term -> Maybe Term
listMkForallTerm _ [] t = return t
listMkForallTerm thy (v : vs) t = do
  u <- listMkForallTerm thy vs t
  mkForallTerm thy v u

listMkForallTermUnsafe :: Theory -> [Var] -> Term -> Term
listMkForallTermUnsafe = mkUnsafe3 "HOL.Syntax.listMkForallTerm" listMkForallTerm
