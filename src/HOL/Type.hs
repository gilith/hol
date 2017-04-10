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
import HOL.Name
import HOL.Data
import qualified HOL.TypeOp as TypeOp

-------------------------------------------------------------------------------
-- The size of a type is the number of TypeData constructors
-------------------------------------------------------------------------------

size :: Type -> Size
size (Type s _) = s

sizeList :: [Type] -> Size
sizeList =
    foldr addSize 0
  where
    addSize ty n = size ty + n

sizeData :: TypeData -> Size
sizeData (VarType _) = 1
sizeData (OpType _ tys) = sizeList tys + 1

-------------------------------------------------------------------------------
-- Constructors and destructors
-------------------------------------------------------------------------------

dest :: Type -> TypeData
dest (Type _ d) = d

mk :: TypeData -> Type
mk d = Type (sizeData d) d

-- Variables

mkVar :: TypeVar -> Type
mkVar v = mk (VarType v)

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
mkOp t tys = mk (OpType t tys)

destOp :: Type -> Maybe (TypeOp,[Type])
destOp ty =
    case dest ty of
      OpType t tys -> Just (t,tys)
      _ -> Nothing

isOp :: Type -> Bool
isOp = isJust . destOp

destTypeOp :: TypeOp -> Type -> Maybe [Type]
destTypeOp t ty =
    case destOp ty of
      Just (u,tys) -> if u == t then Just tys else Nothing
      Nothing -> Nothing

isTypeOp :: TypeOp -> Type -> Bool
isTypeOp t = isJust . destTypeOp t

isTypeOpArity :: TypeOp -> Arity -> Type -> Bool
isTypeOpArity t a ty =
    case destTypeOp t ty of
      Just tys -> length tys == a
      Nothing -> False

isNullaryTypeOp :: TypeOp -> Type -> Bool
isNullaryTypeOp t = isTypeOpArity t 0

destUnaryTypeOp :: TypeOp -> Type -> Maybe Type
destUnaryTypeOp t ty =
    case destTypeOp t ty of
      Just [ty0] -> Just ty0
      _ -> Nothing

isUnaryTypeOp :: TypeOp -> Type -> Bool
isUnaryTypeOp t = isJust . destUnaryTypeOp t

destBinaryTypeOp :: TypeOp -> Type -> Maybe (Type,Type)
destBinaryTypeOp t ty =
    case destTypeOp t ty of
      Just [ty0,ty1] -> Just (ty0,ty1)
      _ -> Nothing

isBinaryTypeOp :: TypeOp -> Type -> Bool
isBinaryTypeOp t = isJust . destBinaryTypeOp t

-------------------------------------------------------------------------------
-- Type variables
-------------------------------------------------------------------------------

data Vars = Vars (Set Type) (Set TypeVar)

emptyVars :: Vars
emptyVars = Vars Set.empty Set.empty

setVars :: Vars -> Set TypeVar
setVars (Vars _ vs) = vs

class HasVars a where
  addVars :: a -> Vars -> Vars

  vars :: a -> Set TypeVar
  vars a = setVars (addVars a emptyVars)

instance HasVars TypeVar where
  addVars v (Vars seen vs) = Vars seen (Set.insert v vs)

instance HasVars a => HasVars [a] where
  addVars xs vs = foldr addVars vs xs

instance HasVars a => HasVars (Set a) where
  addVars xs vs = Set.foldr addVars vs xs

instance HasVars Type where
  addVars ty vs =
      if isSeen then vs
      else case dest ty of
             VarType v -> markSeen (addVars v vs)
             OpType _ tys -> markSeen (addVars tys vs)
    where
      isSeen = Set.member ty seen where Vars seen _ = vs
      markSeen (Vars s z) = Vars (Set.insert ty s) z

-------------------------------------------------------------------------------
-- Primitive types
-------------------------------------------------------------------------------

-- Booleans

bool :: Type
bool = mkOp TypeOp.bool []

isBool :: Type -> Bool
isBool = isNullaryTypeOp TypeOp.bool

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
destFun = destBinaryTypeOp TypeOp.fun

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
isInd = isNullaryTypeOp TypeOp.ind

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
