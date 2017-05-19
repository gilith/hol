{- |
module: $Header$
description: Higher order logic types
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.Type
where

import Data.Maybe (isJust)
import System.IO.Unsafe (unsafePerformIO)
import System.Mem.StableName (makeStableName)

import HOL.Data
import qualified HOL.TypeData as TypeData
import qualified HOL.TypeOp as TypeOp
import qualified HOL.TypeVar as TypeVar

-------------------------------------------------------------------------------
-- Constructors and destructors
-------------------------------------------------------------------------------

dest :: Type -> TypeData
dest (Type d _ _ _) = d

mk :: TypeData -> Type
mk d =
    Type d i sz vs
  where
    i = unsafePerformIO (makeStableName $! d)
    sz = TypeData.size d
    vs = TypeVar.vars d

-- Variables

mkVar :: TypeVar -> Type
mkVar = mk . TypeData.mkVar

destVar :: Type -> Maybe TypeVar
destVar = TypeData.destVar . dest

isVar :: Type -> Bool
isVar = isJust . destVar

eqVar :: TypeVar -> Type -> Bool
eqVar v = TypeData.eqVar v . dest

-- Operators

mkOp :: TypeOp -> [Type] -> Type
mkOp t = mk . TypeData.mkOp t

destOp :: Type -> Maybe (TypeOp,[Type])
destOp = TypeData.destOp . dest

isOp :: Type -> Bool
isOp = isJust . destOp

destGivenOp :: TypeOp -> Type -> Maybe [Type]
destGivenOp t = TypeData.destGivenOp t . dest

isGivenOp :: TypeOp -> Type -> Bool
isGivenOp t = isJust . destGivenOp t

-------------------------------------------------------------------------------
-- Size is measured as the number of TypeData constructors
-------------------------------------------------------------------------------

size :: Type -> Size
size (Type _ _ s _) = s

-------------------------------------------------------------------------------
-- Type syntax
-------------------------------------------------------------------------------

isNullaryOp :: TypeOp -> Type -> Bool
isNullaryOp t = TypeData.isNullaryOp t . dest

destUnaryOp :: TypeOp -> Type -> Maybe Type
destUnaryOp t = TypeData.destUnaryOp t . dest

isUnaryOp :: TypeOp -> Type -> Bool
isUnaryOp t = isJust . destUnaryOp t

destBinaryOp :: TypeOp -> Type -> Maybe (Type,Type)
destBinaryOp t = TypeData.destBinaryOp t . dest

isBinaryOp :: TypeOp -> Type -> Bool
isBinaryOp t = isJust . destBinaryOp t

-------------------------------------------------------------------------------
-- Named type variables (used in standard axioms)
-------------------------------------------------------------------------------

alpha :: Type
alpha = mkVar TypeVar.alpha

beta :: Type
beta = mkVar TypeVar.beta

-------------------------------------------------------------------------------
-- Primitive types
-------------------------------------------------------------------------------

-- Booleans

bool :: Type
bool = mkOp TypeOp.bool []

isBool :: Type -> Bool
isBool = isNullaryOp TypeOp.bool

mkPred :: Type -> Type
mkPred a = mkFun a bool

destPred :: Type -> Maybe Type
destPred ty = do
    (a,b) <- destFun ty
    if isBool b then Just a else Nothing

isPred :: Type -> Bool
isPred = isJust . destPred

mkRel :: Type -> Type -> Type
mkRel a b = mkFun a $ mkPred b

destRel :: Type -> Maybe (Type,Type)
destRel ty = do
    (a,p) <- destFun ty
    b <- destPred p
    return (a,b)

isRel :: Type -> Bool
isRel = isJust . destRel

-- Function spaces

mkFun :: Type -> Type -> Type
mkFun d r = mkOp TypeOp.fun [d,r]

destFun :: Type -> Maybe (Type,Type)
destFun = destBinaryOp TypeOp.fun

isFun :: Type -> Bool
isFun = isJust . destFun

domain :: Type -> Maybe Type
domain = fmap fst . destFun

range :: Type -> Maybe Type
range = fmap snd . destFun

listMkFun :: [Type] -> Type -> Type
listMkFun tys ty = foldr mkFun ty tys

stripFun :: Type -> ([Type],Type)
stripFun ty =
    case destFun ty of
      Nothing -> ([],ty)
      Just (d,r) -> let (ds,rb) = stripFun r in (d : ds, rb)

-- Individuals

ind :: Type
ind = mkOp TypeOp.ind []

isInd :: Type -> Bool
isInd = isNullaryOp TypeOp.ind

-------------------------------------------------------------------------------
-- Types of primitive constants
-------------------------------------------------------------------------------

-- Equality

mkEq :: Type -> Type
mkEq a = mkRel a a

destEq :: Type -> Maybe Type
destEq ty = do
    (a,b) <- destRel ty
    if a == b then Just a else Nothing

isEq :: Type -> Bool
isEq = isJust . destEq

-- Hilbert's choice operator

mkSelect :: Type -> Type
mkSelect a = mkFun (mkFun a bool) a

destSelect :: Type -> Maybe Type
destSelect ty = do
    (p,a) <- destFun ty
    b <- destPred p
    if a == b then Just a else Nothing

isSelect :: Type -> Bool
isSelect = isJust . destSelect
