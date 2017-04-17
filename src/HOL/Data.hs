{- |
module: $Header$
description: Datatypes for higher order logic types and terms
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.Data
where

import HOL.Name
import HOL.Size

-------------------------------------------------------------------------------
-- Type variables
-------------------------------------------------------------------------------

data TypeVar =
    TypeVar Name
  deriving (Eq,Ord,Show)

-------------------------------------------------------------------------------
-- Type operators
-------------------------------------------------------------------------------

type Arity = Int

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

-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

data Type =
    Type TypeData Size

data TypeData =
    VarType TypeVar
  | OpType TypeOp [Type]
  deriving (Eq,Ord,Show)

instance Eq Type where
  (Type d1 s1) == (Type d2 s2) = s1 == s2 && d1 == d2

instance Ord Type where
  compare (Type d1 s1) (Type d2 s2) =
    case compare s1 s2 of
      EQ -> compare d1 d2
      x -> x

instance Show Type where
  show (Type d _) = show d

instance Sizable Type where
  size (Type _ s) = s

instance Sizable TypeData where
  size (VarType _) = 1
  size (OpType _ tys) = size tys + 1

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

data Var =
    Var Name Type
  deriving (Eq,Ord,Show)

-------------------------------------------------------------------------------
-- Constants
-------------------------------------------------------------------------------

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

-------------------------------------------------------------------------------
-- Terms
-------------------------------------------------------------------------------

data Term =
    Term TermData Size Type

data TermData =
    ConstTerm Const Type
  | VarTerm Var
  | AppTerm Term Term
  | AbsTerm Var Term
  deriving (Eq,Ord,Show)

instance Eq Term where
  (Term d1 s1 _) == (Term d2 s2 _) = s1 == s2 && d1 == d2

instance Ord Term where
  compare (Term d1 s1 _) (Term d2 s2 _) =
    case compare s1 s2 of
      EQ -> compare d1 d2
      x -> x

instance Show Term where
  show (Term d _ _) = show d

instance Sizable Term where
  size (Term _ s _) = s

instance Sizable TermData where
  size (ConstTerm _ _) = 1
  size (VarTerm _) = 1
  size (AppTerm f x) = size f + size x
  size (AbsTerm _ b) = size b + 1
