{- |
module: $Header$
description: Higher order logic variables
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.Var
where

import HOL.Name
import HOL.Data

-------------------------------------------------------------------------------
-- Constructors and destructors
-------------------------------------------------------------------------------

mk :: Name -> Type -> Var
mk = Var

dest :: Var -> (Name,Type)
dest (Var n ty) = (n,ty)

name :: Var -> Name
name (Var n _) = n

typeOf :: Var -> Type
typeOf (Var _ ty) = ty
