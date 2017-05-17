{- |
module: $Header$
description: Higher order logic constants
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.Const
where

import qualified Data.Foldable as Foldable
import Data.Set (Set)
import qualified Data.Set as Set
import HOL.Name
import HOL.Data

-------------------------------------------------------------------------------
-- Constructors and destructors
-------------------------------------------------------------------------------

name :: Const -> Name
name (Const n _) = n

prov :: Const -> ConstProv
prov (Const _ p) = p

mkUndef :: Name -> Const
mkUndef n = Const n UndefConstProv

isUndef :: Const -> Bool
isUndef (Const _ p) = p == UndefConstProv

-------------------------------------------------------------------------------
-- Collecting constants
-------------------------------------------------------------------------------

class HasConsts a where
  consts :: a -> Set Const

instance HasConsts Const where
  consts = Set.singleton

instance HasConsts a => HasConsts [a] where
  consts = Foldable.foldMap consts

instance HasConsts a => HasConsts (Set a) where
  consts = Foldable.foldMap consts

instance HasConsts TermData where
  consts (ConstTerm c _) = consts c
  consts (VarTerm _) = Set.empty
  consts (AppTerm f x) = Set.union (consts f) (consts x)
  consts (AbsTerm _ b) = consts b

instance HasConsts Term where
  consts (Term d _ _ _ _) = consts d

-------------------------------------------------------------------------------
-- Primitive constants
-------------------------------------------------------------------------------

-- Equality

eqName :: Name
eqName = mkGlobal "="

eq :: Const
eq = mkUndef eqName

-- Hilbert's indefinite choice operator

selectName :: Name
selectName = mkGlobal "select"

select :: Const
select = mkUndef selectName

-- All primitive constants

primitives :: Set Const
primitives = Set.fromList [eq,select]

-------------------------------------------------------------------------------
-- Standard constants
-------------------------------------------------------------------------------

-- Booleans

boolNamespace :: Namespace
boolNamespace = Namespace ["Data","Bool"]

condName :: Name
condName = Name boolNamespace "cond"

conjName :: Name
conjName = Name boolNamespace "/\\"

disjName :: Name
disjName = Name boolNamespace "\\/"

existsName :: Name
existsName = Name boolNamespace "?"

existsUniqueName :: Name
existsUniqueName = Name boolNamespace "?!"

forallName :: Name
forallName = Name boolNamespace "!"

impName :: Name
impName = Name boolNamespace "==>"

negName :: Name
negName = Name boolNamespace "~"

-- Lists

listNamespace :: Namespace
listNamespace = Namespace ["Data","List"]

appendName :: Name
appendName = Name listNamespace "@"

consName :: Name
consName = Name listNamespace "::"

-- Functions

functionNamespace :: Namespace
functionNamespace = Namespace ["Function"]

composeName :: Name
composeName = Name functionNamespace "o"

-- Natural numbers

naturalNamespace :: Namespace
naturalNamespace = Namespace ["Number","Natural"]

addName :: Name
addName = Name naturalNamespace "+"

bit0Name :: Name
bit0Name = Name naturalNamespace "bit0"

bit1Name :: Name
bit1Name = Name naturalNamespace "bit1"

divName :: Name
divName = Name naturalNamespace "div"

geName :: Name
geName = Name naturalNamespace ">="

gtName :: Name
gtName = Name naturalNamespace ">"

leName :: Name
leName = Name naturalNamespace "<="

ltName :: Name
ltName = Name naturalNamespace "<"

modName :: Name
modName = Name naturalNamespace "mod"

multName :: Name
multName = Name naturalNamespace "*"

powerName :: Name
powerName = Name naturalNamespace "^"

subName :: Name
subName = Name naturalNamespace "-"

zeroName :: Name
zeroName = Name naturalNamespace "zero"

-- Sets

setNamespace :: Namespace
setNamespace = Namespace ["Set"]

differenceName :: Name
differenceName = Name setNamespace "difference"

inName :: Name
inName = Name setNamespace "in"

intersectName :: Name
intersectName = Name setNamespace "intersect"

subsetName :: Name
subsetName = Name setNamespace "subset"

unionName :: Name
unionName = Name setNamespace "union"
