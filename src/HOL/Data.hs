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

import Data.Set (Set)
import System.Mem.StableName (StableName)

import HOL.Name

-------------------------------------------------------------------------------
-- Size of types and terms
-------------------------------------------------------------------------------

type Size = Integer

-------------------------------------------------------------------------------
-- Type variables
-------------------------------------------------------------------------------

data TypeVar =
    TypeVar Name
  deriving (Eq,Ord,Show)

-------------------------------------------------------------------------------
-- Type operators
-------------------------------------------------------------------------------

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

data Type = Type TypeData TypeId Size (Set TypeVar)

data TypeData =
    VarType TypeVar
  | OpType TypeOp [Type]
  deriving (Eq,Ord,Show)

type TypeId = StableName TypeData

instance Eq Type where
  (Type d1 i1 s1 _) == (Type d2 i2 s2 _) =
      s1 == s2 && (i1 == i2 || d1 == d2)

instance Ord Type where
  compare (Type d1 i1 s1 _) (Type d2 i2 s2 _) =
      case compare s1 s2 of
        EQ -> if i1 == i2 then EQ else compare d1 d2
        x -> x

instance Show Type where
  show (Type _ _ s _) = show $ "Type<" ++ show s ++ ">"

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
  | AbsConstProv TypeOpDef
  | RepConstProv TypeOpDef
  deriving (Eq,Ord,Show)

data ConstDef =
    ConstDef Term
  deriving (Eq,Ord,Show)

-------------------------------------------------------------------------------
-- Terms
-------------------------------------------------------------------------------

data Term = Term TermData TermId Size Type (Set TypeVar) (Set Var)

data TermData =
    ConstTerm Const Type
  | VarTerm Var
  | AppTerm Term Term
  | AbsTerm Var Term
  deriving (Eq,Ord,Show)

type TermId = StableName TermData

instance Eq Term where
  (Term d1 i1 s1 _ _ _) == (Term d2 i2 s2 _ _ _) =
      s1 == s2 && (i1 == i2 || d1 == d2)

instance Ord Term where
  compare (Term d1 i1 s1 _ _ _) (Term d2 i2 s2 _ _ _) =
      case compare s1 s2 of
        EQ -> if i1 == i2 then EQ else compare d1 d2
        x -> x

instance Show Term where
  show (Term _ _ s _ _ _) = show $ "Term<" ++ show s ++ ">"
