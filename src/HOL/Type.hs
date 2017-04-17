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
import Data.Set (Set)
import qualified Data.Set as Set
import HOL.Data
import HOL.Size
import qualified HOL.TypeOp as TypeOp

-------------------------------------------------------------------------------
-- Constructors and destructors
-------------------------------------------------------------------------------

dest :: Type -> TypeData
dest (Type d _) = d

mk :: TypeData -> Type
mk d = Type d (size d)

-- Variables

mkVar :: TypeVar -> Type
mkVar v = mk $ VarType v

destVar :: Type -> Maybe TypeVar
destVar ty =
    case dest ty of
      VarType v -> Just v
      _ -> Nothing

isVar :: Type -> Bool
isVar = isJust . destVar

equalVar :: TypeVar -> Type -> Bool
equalVar v ty =
    case destVar ty of
      Just w -> w == v
      Nothing -> False

-- Operators

mkOp :: TypeOp -> [Type] -> Type
mkOp t tys = mk $ OpType t tys

destOp :: Type -> Maybe (TypeOp,[Type])
destOp ty =
    case dest ty of
      OpType t tys -> Just (t,tys)
      _ -> Nothing

isOp :: Type -> Bool
isOp = isJust . destOp

destGivenOp :: TypeOp -> Type -> Maybe [Type]
destGivenOp t ty =
    case destOp ty of
      Just (u,tys) -> if u == t then Just tys else Nothing
      Nothing -> Nothing

isGivenOp :: TypeOp -> Type -> Bool
isGivenOp t = isJust . destGivenOp t

isNullaryOp :: TypeOp -> Type -> Bool
isNullaryOp t ty =
    case destGivenOp t ty of
      Just tys -> null tys
      Nothing -> False

destUnaryOp :: TypeOp -> Type -> Maybe Type
destUnaryOp t ty =
    case destGivenOp t ty of
      Just [ty0] -> Just ty0
      _ -> Nothing

isUnaryOp :: TypeOp -> Type -> Bool
isUnaryOp t = isJust . destUnaryOp t

destBinaryOp :: TypeOp -> Type -> Maybe (Type,Type)
destBinaryOp t ty =
    case destGivenOp t ty of
      Just [ty0,ty1] -> Just (ty0,ty1)
      _ -> Nothing

isBinaryOp :: TypeOp -> Type -> Bool
isBinaryOp t = isJust . destBinaryOp t

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
