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

import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint ((<>),(<+>))
import qualified Text.PrettyPrint as PP

import qualified HOL.Const as Const
import HOL.Data
import HOL.Name
import HOL.Sequent (Sequent)
import qualified HOL.Sequent as Sequent
import qualified HOL.Term as Term
import HOL.TermAlpha (TermAlpha)
import qualified HOL.TermAlpha as TermAlpha
import HOL.Thm (Thm)
import qualified HOL.Thm as Thm
import qualified HOL.Type as Type
import qualified HOL.TypeOp as TypeOp
import qualified HOL.TypeVar as TypeVar
import qualified HOL.Var as Var

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

instance Printable Integer where
  toDoc = PP.integer

instance Printable a => Printable [a] where
  toDoc = PP.brackets . PP.fsep . PP.punctuate PP.comma . map toDoc

instance Printable a => Printable (Set a) where
  toDoc = PP.braces . PP.fsep . PP.punctuate PP.comma . map toDoc . Set.toList

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
  toDoc = toDoc . TypeVar.dest

instance Printable TypeOp where
  toDoc = toDoc . TypeOp.name

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

-------------------------------------------------------------------------------
-- Terms
-------------------------------------------------------------------------------

instance Printable Const where
  toDoc = toDoc . Const.name

instance Printable Var where
  toDoc = toDoc . Var.name

instance Printable Term where
  toDoc =
      normal
    where
      basic tm =
          case Term.dest tm of
            VarTerm v -> toDoc v
            ConstTerm c _ -> toDoc c
            _ -> parens tm

      application tm =
          case Term.dest tm of
            AppTerm f x -> application f <+> basic x
            _ -> basic tm

      normal tm =
          case Term.dest tm of
            AbsTerm v b -> PP.text "\\" <> toDoc v <> PP.text "." <+> normal b
            _ -> application tm

      parens = PP.parens . normal

instance Printable TermAlpha where
  toDoc = toDoc . TermAlpha.dest

-------------------------------------------------------------------------------
-- Theorems
-------------------------------------------------------------------------------

instance Printable Sequent where
  toDoc sq =
      hd <+> PP.text "|-" <+> toDoc c
    where
      (h,c) = Sequent.dest sq
      hd = if Set.null h then PP.empty else toDoc h

instance Printable Thm where
  toDoc = toDoc . Thm.dest
