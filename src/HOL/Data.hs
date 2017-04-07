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

import HOL.Name

type Size = Integer

data Type =
    Type Size TypeData
  deriving (Eq,Ord,Show)

data TypeData =
    VarType TypeVar
  | OpType TypeOp [Type]
  deriving (Eq,Ord,Show)

data TypeVar =
    TypeVar Name
  deriving (Eq,Ord,Show)

data TypeOp =
    TypeOp Name TypeOpProv
  deriving (Eq,Ord,Show)

data TypeOpProv =
    UndefTypeOpProv
  | DefTypeOpProv TypeOpDef
  deriving (Eq,Ord,Show)

data TypeOpDef =
    TypeOpDef Term [TypeVar]
  deriving (Eq,Ord,Show)

data Var =
    Var Name Type
  deriving (Eq,Ord,Show)

data Term =
    Term Size TermData Type
  deriving (Eq,Ord,Show)

data TermData =
    ConstTerm Const Type
  | VarTerm Var
  | AppTerm Term Term
  | AbsTerm Var Term
  deriving (Eq,Ord,Show)

data Const =
    Const Name ConstProv
  deriving (Eq,Ord,Show)

data ConstProv =
    UndefConstProv
  | DefConstProv ConstDef
  | AbsConstProv TypeOp
  | RepConstProv TypeOp
  deriving (Eq,Ord,Show)

data ConstDef =
    ConstDef Term
  deriving (Eq,Ord,Show)
