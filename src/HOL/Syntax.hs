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

import Control.Monad (guard)
import Data.Maybe (isJust)

import qualified HOL.Const as Const
import HOL.Data (Const,Term,Type,TypeOp,Var)
--import HOL.Name (Name)
--import qualified HOL.Name as Name
--import HOL.Print (toString)
--import HOL.Term (renameFresh)
import qualified HOL.Term as Term
import HOL.Theory (Theory)
import qualified HOL.Theory as Theory
import qualified HOL.Type as Type
import qualified HOL.TypeOp as TypeOp
import HOL.Util (mkUnsafe1,mkUnsafe2,mkUnsafe3)
import qualified HOL.Var as Var

-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

mkUnaryType :: Type -> Type
mkUnaryType a = Type.mkFun a a

mkBinaryType :: Type -> Type
mkBinaryType a = Type.mkFun a (mkUnaryType a)

mkUnaryRelationType :: Type -> Type
mkUnaryRelationType a = Type.mkFun a Type.bool

mkBinaryRelationType :: Type -> Type
mkBinaryRelationType a = Type.mkFun a (mkUnaryRelationType a)

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

isTrueTerm :: Term -> Bool
isTrueTerm tm = isJust $ do
  (c,_) <- Term.destConst tm
  guard (Const.name c == Const.trueName)
  return $ Just ()

-- Falsity

falseConst :: Theory -> Maybe Const
falseConst thy = Theory.lookupConst thy Const.falseName

falseTerm :: Theory -> Maybe Term
falseTerm thy = do
    c <- falseConst thy
    return $ Term.mkConst c Type.bool

falseTermUnsafe :: Theory -> Term
falseTermUnsafe = mkUnsafe1 "HOL.Syntax.falseTerm" falseTerm

isFalseTerm :: Term -> Bool
isFalseTerm tm = isJust $ do
  (c,_) <- Term.destConst tm
  guard (Const.name c == Const.falseName)
  return $ Just ()

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

destNegTerm :: Term -> Maybe Term
destNegTerm tm = do
  (c,t) <- Term.destUnaryOp tm
  guard (Const.name c == Const.negName)
  return t

-- Conjunction

conjConst :: Theory -> Maybe Const
conjConst thy = Theory.lookupConst thy Const.conjName

conjTerm :: Theory -> Maybe Term
conjTerm thy = do
  c <- conjConst thy
  return $ Term.mkConst c (mkBinaryType Type.bool)

mkConjTerm :: Theory -> Term -> Term -> Maybe Term
mkConjTerm thy t u = do
  c <- conjTerm thy
  Term.listMkApp c [t,u]

mkConjTermUnsafe :: Theory -> Term -> Term -> Term
mkConjTermUnsafe = mkUnsafe3 "HOL.Syntax.mkConjTerm" mkConjTerm

destConjTerm :: Term -> Maybe (Term,Term)
destConjTerm tm = do
  (c,t,u) <- Term.destBinaryOp tm
  guard (Const.name c == Const.conjName)
  return (t,u)

destConjTermUnsafe :: Term -> (Term,Term)
destConjTermUnsafe = mkUnsafe1 "HOL.Syntax.destConjTerm" destConjTerm

-- Disjunction

disjConst :: Theory -> Maybe Const
disjConst thy = Theory.lookupConst thy Const.disjName

disjTerm :: Theory -> Maybe Term
disjTerm thy = do
  c <- disjConst thy
  return $ Term.mkConst c (mkBinaryType Type.bool)

mkDisjTerm :: Theory -> Term -> Term -> Maybe Term
mkDisjTerm thy t u = do
  c <- disjTerm thy
  Term.listMkApp c [t,u]

mkDisjTermUnsafe :: Theory -> Term -> Term -> Term
mkDisjTermUnsafe = mkUnsafe3 "HOL.Syntax.mkDisjTerm" mkDisjTerm

destDisjTerm :: Term -> Maybe (Term,Term)
destDisjTerm tm = do
  (c,t,u) <- Term.destBinaryOp tm
  guard (Const.name c == Const.disjName)
  return (t,u)

destDisjTermUnsafe :: Term -> (Term,Term)
destDisjTermUnsafe = mkUnsafe1 "HOL.Syntax.destDisjTerm" destDisjTerm

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

destImpTerm :: Term -> Maybe (Term,Term)
destImpTerm tm = do
  (c,t,u) <- Term.destBinaryOp tm
  guard (Const.name c == Const.impName)
  return (t,u)

destImpTermUnsafe :: Term -> (Term,Term)
destImpTermUnsafe = mkUnsafe1 "HOL.Syntax.destImpTerm" destImpTerm

-- Existential quantification

existsConst :: Theory -> Maybe Const
existsConst thy = Theory.lookupConst thy Const.existsName

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

destExistsTerm :: Term -> Maybe (Var,Term)
destExistsTerm tm = do
    (c,t) <- Term.destUnaryOp tm
    (v,b) <- Term.destAbs t
    guard (Const.name c == Const.existsName)
    return (v,b)

stripExistsTerm :: Term -> ([Var],Term)
stripExistsTerm tm =
    case destExistsTerm tm of
      Just (v,t) -> (v : vs, b) where (vs,b) = stripExistsTerm t
      Nothing -> ([],tm)

-- Universal quantification

forallConst :: Theory -> Maybe Const
forallConst thy = Theory.lookupConst thy Const.forallName

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

destForallTerm :: Term -> Maybe (Var,Term)
destForallTerm tm = do
    (c,t) <- Term.destUnaryOp tm
    (v,b) <- Term.destAbs t
    guard (Const.name c == Const.forallName)
    return (v,b)

stripForallTerm :: Term -> ([Var],Term)
stripForallTerm tm =
    case destForallTerm tm of
      Just (v,t) -> (v : vs, b) where (vs,b) = stripForallTerm t
      Nothing -> ([],tm)

-------------------------------------------------------------------------------
-- Natural numbers
-------------------------------------------------------------------------------

-- Types

naturalTypeOp :: Theory -> Maybe TypeOp
naturalTypeOp thy = Theory.lookupTypeOp thy TypeOp.naturalName

naturalType :: Theory -> Maybe Type
naturalType thy = do
  t <- naturalTypeOp thy
  return $ Type.mkOp t []

naturalTypeUnsafe :: Theory -> Type
naturalTypeUnsafe = mkUnsafe1 "HOL.Syntax.naturalType" naturalType

-- Zero

zeroConst :: Theory -> Maybe Const
zeroConst thy = Theory.lookupConst thy Const.zeroName

zeroTerm :: Theory -> Maybe Term
zeroTerm thy = do
  c <- zeroConst thy
  ty <- naturalType thy
  return $ Term.mkConst c ty

zeroTermUnsafe :: Theory -> Term
zeroTermUnsafe = mkUnsafe1 "HOL.Syntax.zeroTerm" zeroTerm

isZeroTerm :: Term -> Bool
isZeroTerm tm =
    case Term.destConst tm of
      Just (c,_) -> Const.name c == Const.zeroName
      Nothing -> False

-- Successor

sucConst :: Theory -> Maybe Const
sucConst thy = Theory.lookupConst thy Const.sucName

sucTerm :: Theory -> Maybe Term
sucTerm thy = do
  c <- sucConst thy
  ty <- fmap mkUnaryType $ naturalType thy
  return $ Term.mkConst c ty

mkSucTerm :: Theory -> Term -> Maybe Term
mkSucTerm thy t = do
  f <- sucTerm thy
  Term.mkApp f t

mkSucTermUnsafe :: Theory -> Term -> Term
mkSucTermUnsafe = mkUnsafe2 "HOL.Syntax.mkSucTerm" mkSucTerm

destSucTerm :: Term -> Maybe Term
destSucTerm tm = do
  (c,t) <- Term.destUnaryOp tm
  guard (Const.name c == Const.sucName)
  return t

-- Addition

addConst :: Theory -> Maybe Const
addConst thy = Theory.lookupConst thy Const.addName

addTerm :: Theory -> Maybe Term
addTerm thy = do
  c <- addConst thy
  ty <- fmap mkBinaryType $ naturalType thy
  return $ Term.mkConst c ty

mkAddTerm :: Theory -> Term -> Term -> Maybe Term
mkAddTerm thy t u = do
  f <- addTerm thy
  Term.listMkApp f [t,u]

mkAddTermUnsafe :: Theory -> Term -> Term -> Term
mkAddTermUnsafe = mkUnsafe3 "HOL.Syntax.mkAddTerm" mkAddTerm

destAddTerm :: Term -> Maybe (Term,Term)
destAddTerm tm = do
  (c,t,u) <- Term.destBinaryOp tm
  guard (Const.name c == Const.addName)
  return (t,u)

destAddTermUnsafe :: Term -> (Term,Term)
destAddTermUnsafe = mkUnsafe1 "HOL.Syntax.destAddTerm" destAddTerm

-- Less than or equal to

leConst :: Theory -> Maybe Const
leConst thy = Theory.lookupConst thy Const.leName

leTerm :: Theory -> Maybe Term
leTerm thy = do
  c <- leConst thy
  ty <- fmap mkBinaryRelationType $ naturalType thy
  return $ Term.mkConst c ty

mkLeTerm :: Theory -> Term -> Term -> Maybe Term
mkLeTerm thy t u = do
  c <- leTerm thy
  Term.listMkApp c [t,u]

mkLeTermUnsafe :: Theory -> Term -> Term -> Term
mkLeTermUnsafe = mkUnsafe3 "HOL.Syntax.mkLeTerm" mkLeTerm

destLeTerm :: Term -> Maybe (Term,Term)
destLeTerm tm = do
  (c,t,u) <- Term.destBinaryOp tm
  guard (Const.name c == Const.leName)
  return (t,u)

destLeTermUnsafe :: Term -> (Term,Term)
destLeTermUnsafe = mkUnsafe1 "HOL.Syntax.destLeTerm" destLeTerm

-- Less than

ltConst :: Theory -> Maybe Const
ltConst thy = Theory.lookupConst thy Const.ltName

ltTerm :: Theory -> Maybe Term
ltTerm thy = do
  c <- ltConst thy
  ty <- fmap mkBinaryRelationType $ naturalType thy
  return $ Term.mkConst c ty

mkLtTerm :: Theory -> Term -> Term -> Maybe Term
mkLtTerm thy t u = do
  c <- ltTerm thy
  Term.listMkApp c [t,u]

mkLtTermUnsafe :: Theory -> Term -> Term -> Term
mkLtTermUnsafe = mkUnsafe3 "HOL.Syntax.mkLtTerm" mkLtTerm

destLtTerm :: Term -> Maybe (Term,Term)
destLtTerm tm = do
  (c,t,u) <- Term.destBinaryOp tm
  guard (Const.name c == Const.ltName)
  return (t,u)

destLtTermUnsafe :: Term -> (Term,Term)
destLtTermUnsafe = mkUnsafe1 "HOL.Syntax.destLtTerm" destLtTerm

-- Multiplication

multConst :: Theory -> Maybe Const
multConst thy = Theory.lookupConst thy Const.multName

multTerm :: Theory -> Maybe Term
multTerm thy = do
  c <- multConst thy
  ty <- fmap mkBinaryType $ naturalType thy
  return $ Term.mkConst c ty

mkMultTerm :: Theory -> Term -> Term -> Maybe Term
mkMultTerm thy t u = do
  f <- multTerm thy
  Term.listMkApp f [t,u]

mkMultTermUnsafe :: Theory -> Term -> Term -> Term
mkMultTermUnsafe = mkUnsafe3 "HOL.Syntax.mkMultTerm" mkMultTerm

destMultTerm :: Term -> Maybe (Term,Term)
destMultTerm tm = do
  (c,t,u) <- Term.destBinaryOp tm
  guard (Const.name c == Const.multName)
  return (t,u)

destMultTermUnsafe :: Term -> (Term,Term)
destMultTermUnsafe = mkUnsafe1 "HOL.Syntax.destMultTerm" destMultTerm

-- Divides relation

dividesConst :: Theory -> Maybe Const
dividesConst thy = Theory.lookupConst thy Const.dividesName

dividesTerm :: Theory -> Maybe Term
dividesTerm thy = do
  c <- dividesConst thy
  ty <- fmap mkBinaryRelationType $ naturalType thy
  return $ Term.mkConst c ty

mkDividesTerm :: Theory -> Term -> Term -> Maybe Term
mkDividesTerm thy t u = do
  c <- dividesTerm thy
  Term.listMkApp c [t,u]

mkDividesTermUnsafe :: Theory -> Term -> Term -> Term
mkDividesTermUnsafe = mkUnsafe3 "HOL.Syntax.mkDividesTerm" mkDividesTerm

destDividesTerm :: Term -> Maybe (Term,Term)
destDividesTerm tm = do
  (c,t,u) <- Term.destBinaryOp tm
  guard (Const.name c == Const.dividesName)
  return (t,u)

destDividesTermUnsafe :: Term -> (Term,Term)
destDividesTermUnsafe = mkUnsafe1 "HOL.Syntax.destDividesTerm" destDividesTerm

-- Numerals

bit0Const :: Theory -> Maybe Const
bit0Const thy = Theory.lookupConst thy Const.bit0Name

bit1Const :: Theory -> Maybe Const
bit1Const thy = Theory.lookupConst thy Const.bit1Name

bit0Term :: Theory -> Maybe Term
bit0Term thy = do
  c <- bit0Const thy
  ty <- fmap mkUnaryType $ naturalType thy
  return $ Term.mkConst c ty

bit1Term :: Theory -> Maybe Term
bit1Term thy = do
  c <- bit1Const thy
  ty <- fmap mkUnaryType $ naturalType thy
  return $ Term.mkConst c ty

bitTerm :: Theory -> Bool -> Maybe Term
bitTerm thy True = bit1Term thy
bitTerm thy False = bit0Term thy

mkBitTerm :: Theory -> Bool -> Term -> Maybe Term
mkBitTerm thy b t = do
  f <- bitTerm thy b
  Term.mkApp f t

destBitTerm :: Term -> Maybe (Bool,Term)
destBitTerm tm = do
    (c,t) <- Term.destUnaryOp tm
    fmap (flip (,) t) $ bit (Const.name c)
  where
    bit n = if n == Const.bit0Name then Just False
            else if n == Const.bit1Name then Just True
            else Nothing

mkNumeralTerm :: Theory -> Integer -> Maybe Term
mkNumeralTerm thy 0 = zeroTerm thy
mkNumeralTerm thy i = do
    t <- mkNumeralTerm thy (i `div` 2)
    mkBitTerm thy (odd i) t

mkNumeralTermUnsafe :: Theory -> Integer -> Term
mkNumeralTermUnsafe = mkUnsafe2 "HOL.Syntax.mkNumeralTerm" mkNumeralTerm

destNumeralTerm :: Term -> Maybe Integer
destNumeralTerm tm =
    if isZeroTerm tm then Just 0
    else do
      (b,t) <- destBitTerm tm
      i <- destNumeralTerm t
      bit b i
  where
    bit False 0 = Nothing
    bit b i = Just (2 * i + (if b then 1 else 0))

isNumeralTerm :: Term -> Bool
isNumeralTerm = isJust . destNumeralTerm
