{- |
module: $Header$
description: Pretty-printing
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.Print
where

import Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as PP

import HOL.Data
import HOL.Name
import qualified HOL.Type as Type

-------------------------------------------------------------------------------
-- Printable types
-------------------------------------------------------------------------------

class Printable a where
  toDoc :: a -> PP.Doc

  toString :: a -> String
  toString =
      PP.renderStyle style . toDoc
    where
      style = PP.style {PP.lineLength = 80}

-------------------------------------------------------------------------------
-- Names
-------------------------------------------------------------------------------

instance Printable Namespace where
  toDoc =
      go
    where
      go (Namespace []) = pr0
      go (Namespace l) = pr1 l

      pr0 = PP.text "<empty>"
      pr1 = PP.hcat . PP.punctuate (PP.text ".") . map PP.text

instance Printable Name where
  toDoc (Name (Namespace l) s) = toDoc (Namespace (l ++ [s]))

-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

instance Printable TypeVar where
  toDoc (TypeVar n) = toDoc n

instance Printable TypeOp where
  toDoc (TypeOp n _) = toDoc n

instance Printable Type where
  toDoc =
      normal
    where
      basic ty =
         if Type.isFun ty then PP.parens $ normal ty
         else case Type.dest ty of
                VarType v -> toDoc v
                OpType t [] -> toDoc t
                OpType t [x] -> basic x <+> toDoc t
                OpType t xs -> normals xs <+> toDoc t

      normal ty =
        case Type.destFun ty of
          Just (d,r) -> basic d <+> PP.char '\8594' <+> normal r
          Nothing -> basic ty

      normals = PP.parens . PP.fsep . PP.punctuate (PP.text ",") . map normal
