{- |
module: $Header$
description: Higher order logic type data
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.TypeData
where

import qualified Data.List as List
import Data.Maybe (isJust)

import HOL.Data

-------------------------------------------------------------------------------
-- Constructors and destructors
-------------------------------------------------------------------------------

-- Variables

mkVar :: TypeVar -> TypeData
mkVar = VarType

destVar :: TypeData -> Maybe TypeVar
destVar (VarType v) = Just v
destVar _ = Nothing

isVar :: TypeData -> Bool
isVar = isJust . destVar

eqVar :: TypeVar -> TypeData -> Bool
eqVar v d =
    case destVar d of
      Just w -> w == v
      Nothing -> False

-- Operators

mkOp :: TypeOp -> [Type] -> TypeData
mkOp = OpType

destOp :: TypeData -> Maybe (TypeOp,[Type])
destOp (OpType t tys) = Just (t,tys)
destOp _ = Nothing

isOp :: TypeData -> Bool
isOp = isJust . destOp

destGivenOp :: TypeOp -> TypeData -> Maybe [Type]
destGivenOp t d =
    case destOp d of
      Just (u,tys) -> if u == t then Just tys else Nothing
      Nothing -> Nothing

isGivenOp :: TypeOp -> TypeData -> Bool
isGivenOp t = isJust . destGivenOp t

-------------------------------------------------------------------------------
-- Size is measured as the number of TypeData constructors
-------------------------------------------------------------------------------

size :: TypeData -> Size
size (VarType _) = 1
size (OpType _ tys) =
    List.foldl' add 1 tys
  where
    add n (Type _ _ s _) = n + s

-------------------------------------------------------------------------------
-- Type syntax
-------------------------------------------------------------------------------

isNullaryOp :: TypeOp -> TypeData -> Bool
isNullaryOp t d =
    case destGivenOp t d of
      Just tys -> null tys
      Nothing -> False

destUnaryOp :: TypeOp -> TypeData -> Maybe Type
destUnaryOp t d =
    case destGivenOp t d of
      Just [ty] -> Just ty
      _ -> Nothing

isUnaryOp :: TypeOp -> TypeData -> Bool
isUnaryOp t = isJust . destUnaryOp t

destBinaryOp :: TypeOp -> TypeData -> Maybe (Type,Type)
destBinaryOp t d =
    case destGivenOp t d of
      Just [ty0,ty1] -> Just (ty0,ty1)
      _ -> Nothing

isBinaryOp :: TypeOp -> TypeData -> Bool
isBinaryOp t = isJust . destBinaryOp t
