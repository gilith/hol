{- |
module: $Header$
description: Mutually recursive datatypes of higher order logic types and terms
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.Data
where

type Name = String

data Type = Type TypeData Integer

data TypeData =
    VarType TypeVar
  | OpType TypeOp [Type]

data TypeVar = TypeVar Name

data TypeOp = TypeOp Name TypeOpProv

data TypeOpProv =
    UndefTypeOpProv
  | DefTypeOpProv TypeOpDef

data TypeOpDef = TypeOpDef Term [TypeVar]

data Var = Var Name Type

data Term = Term TermData Type Integer

data TermData =
    ConstTerm Const Type
  | VarTerm Var
  | AppTerm Term Term
  | AbsTerm Var Term

data Const = Const Name ConstProv

data ConstProv =
    UndefConstProv
  | DefConstProv ConstDef
  | AbsConstProv TypeOp
  | RepConstProv TypeOp

data ConstDef = ConstDef Term
