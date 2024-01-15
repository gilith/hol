{- |
module: $Header$
description: Higher order logic interface to TPTP format
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.Tptp
where

import Control.Monad (guard)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)
import Data.Set (Set)
import qualified Data.Set as Set
import Prelude hiding ((<>))
import Text.PrettyPrint ((<>),(<+>),Doc)
import qualified Text.PrettyPrint as PP

import qualified HOL.Const as Const
import HOL.Data
import HOL.Name
import HOL.Print
import qualified HOL.Term as Term
import qualified HOL.Type as Type

-------------------------------------------------------------------------------
-- TPTP roles
-------------------------------------------------------------------------------

data Role =
    AxiomRole
  | ConjectureRole
  | DefinitionRole
  | TheoremRole
  deriving (Eq,Ord,Show)

toStringRole :: Role -> String
toStringRole AxiomRole = "axiom"
toStringRole ConjectureRole = "conjecture"
toStringRole DefinitionRole = "definition"
toStringRole TheoremRole = "theorem"

instance Printable Role where
  toDoc = PP.text . toStringRole

-------------------------------------------------------------------------------
-- TPTP formulas
-------------------------------------------------------------------------------

data Formula =
    Formula
      {nameFormula :: String,
       roleFormula :: Role,
       bodyFormula :: Term}
  deriving (Eq,Ord,Show)

-------------------------------------------------------------------------------
-- Formula construction
-------------------------------------------------------------------------------

mkFormula :: Role -> String -> Int -> Term -> Formula
mkFormula r p i t =
    Formula {nameFormula = p ++ show i,
             roleFormula = r,
             bodyFormula = t}

mkFormulas :: Role -> String -> [Term] -> [Formula]
mkFormulas r p = zipWith (mkFormula r p) [0..]

mkTheorems :: String -> [Term] -> [Formula]
mkTheorems = mkFormulas TheoremRole

mkConjecture :: String -> Term -> Formula
mkConjecture n t =
    Formula {nameFormula = n,
             roleFormula = ConjectureRole,
             bodyFormula = t}

-------------------------------------------------------------------------------
-- Formula printing
-------------------------------------------------------------------------------

instance Printable Formula where
  toDoc fm =
      PP.text "fof" <>
      PP.lparen <>
      PP.fsep (commas [PP.text (nameFormula fm),
                       toDoc (roleFormula fm),
                       normal (bodyFormula fm)]) <+>
      PP.rparen <>
      PP.char '.'
    where
      commas = PP.punctuate PP.comma

      atom tm =
          case Term.dest tm of
            VarTerm v -> toDoc v
            ConstTerm c _ -> ppConst c
            _ -> parens tm

      basic tm =
          case destNumeral tm of
            Just i -> PP.integer i
            Nothing -> atom tm

      application tm =
          case stripGenApp tm of
            (_,[]) -> basic tm
            (f,xs) -> basic f <> PP.parens (PP.sep (commas (map basic xs)))

      negation _ tm =
          case stripNegation tm of
            ([],_) -> application tm
            (ns,t) -> ppPrefixOps ns $ application t

      infixTerm = ppInfixOps destInfix negation

      binder tm =
          case destBinder tm of
            Just (b,v,t) -> ppBinder b (map basic v) (negation True t)
            Nothing -> infixTerm True tm

      normal = binder

      parens tm = PP.lparen <+> normal tm <+> PP.rparen

      -------------------------------------------------------------------------
      -- These grammar tables control term printing
      -------------------------------------------------------------------------

      constantTable :: [(Name, String)]
      constantTable =
          [(Const.falseName, "$false"),
           (Const.trueName, "$true")]

      infixTable :: [(Name, Prec, Assoc, Maybe String)]
      infixTable =
          [(Const.conjName, -1, RightAssoc, Nothing),
           (Const.disjName, -1, RightAssoc, Nothing),
           (Const.impName, -3, NonAssoc, Just "=>")]

      quantifierTable :: [(Name, Maybe String)]
      quantifierTable =
          [(Const.forallName, Nothing),
           (Const.existsName, Nothing)]

      negationTable :: [(Name, Maybe String)]
      negationTable =
          [(Const.negName, Nothing)]

      -------------------------------------------------------------------------
      -- Constants
      -------------------------------------------------------------------------

      constants :: Map Name Doc
      constants = Map.fromList $ map mkConst constantTable

      mkConst :: (Name,String) -> (Name,Doc)
      mkConst (n,s) = (n, PP.text s)

      ppConst :: Const -> Doc
      ppConst c = case Map.lookup (Const.name c) constants of
                    Just d -> d
                    Nothing -> toDoc c

      -------------------------------------------------------------------------
      -- Infix operators
      -------------------------------------------------------------------------

      nameOp :: Name -> Maybe String -> String
      nameOp n x =
          case x of
            Just y -> y
            Nothing -> let Name _ y = n in y

      mkInfixOp :: (Name, Prec, Assoc, Maybe String) -> (Name,InfixOp)
      mkInfixOp (n,p,a,x) =
          (n, (p, a, flip (<+>) d))
        where
          s = nameOp n x
          t = PP.text s
          d = if isSymbolString s then t else PP.char '`' <> t <> PP.char '`'

      eqInfixOp :: InfixOp
      eqInfixOp = snd $ mkInfixOp (Const.eqName, 3, NonAssoc, Nothing)

      iffInfixOp :: InfixOp
      iffInfixOp = snd $ mkInfixOp (Const.eqName, -3, NonAssoc, Just "<=>")

      infixOps :: Map Name InfixOp
      infixOps = Map.fromList $ map mkInfixOp infixTable

      destInfix :: Term -> Maybe (InfixOp,Term,Term)
      destInfix tm = do
          (c,x,y) <- Term.destBinaryOp tm
          i <- lookupOp (Term.typeOf x) (Const.name c)
          return (i,x,y)
        where
          lookupOp ty n =
              if n /= Const.eqName then Map.lookup n infixOps
              else if Type.isBool ty then Just iffInfixOp
              else Just eqInfixOp

      isInfix :: Term -> Bool
      isInfix = isJust . destInfix

      -------------------------------------------------------------------------
      -- Prefix operators
      -------------------------------------------------------------------------

      mkPrefixOp :: (Name, Maybe String) -> (Name,PrefixOp)
      mkPrefixOp (n,x) =
          (n, attach $ PP.text s)
        where
          s = nameOp n x
          attach = (<+>)

      -------------------------------------------------------------------------
      -- Quantifiers
      -------------------------------------------------------------------------

      quantifiers :: Map Name PrefixOp
      quantifiers = Map.fromList $ map mkPrefixOp quantifierTable

      destQuantifier :: Term -> Maybe (Const,Term,Term)
      destQuantifier tm = do
          (c,vb) <- Term.destUnaryOp tm
          (v,b) <- Term.destAbs vb
          return (c, Term.mkVar v, b)

      stripQuantifier :: Term -> Maybe (PrefixOp,[Term],Term)
      stripQuantifier tm = do
          (c,v,t) <- destQuantifier tm
          q <- Map.lookup (Const.name c) quantifiers
          let (vs,b) = strip c t
          return (q, v : vs, b)
        where
          strip c t =
              case destQuantifier t of
                Just (c',v,u) | c' == c -> (v : vs, b) where (vs,b) = strip c u
                _ -> ([],t)

      -------------------------------------------------------------------------
      -- Binders
      -------------------------------------------------------------------------

      destBinder :: Term -> Maybe (PrefixOp,[Term],Term)
      destBinder = stripQuantifier

      isBinder :: Term -> Bool
      isBinder = isJust . destBinder

      ppBoundVars :: [PP.Doc] -> PP.Doc
      ppBoundVars v = PP.brackets (PP.fcat (commas v)) <+> PP.colon

      ppBinder :: PrefixOp -> [PP.Doc] -> PP.Doc -> PP.Doc
      ppBinder b v t = b $ PP.sep [ppBoundVars v, t]

      -------------------------------------------------------------------------
      -- Negation operators
      -------------------------------------------------------------------------

      negations :: Map Name PrefixOp
      negations = Map.fromList $ map mkPrefixOp negationTable

      destNegation :: Term -> Maybe (PrefixOp,Term)
      destNegation tm = do
          (c,t) <- Term.destUnaryOp tm
          p <- Map.lookup (Const.name c) negations
          return (p,t)

      isNegation :: Term -> Bool
      isNegation = isJust . destNegation

      stripNegation :: Term -> ([PrefixOp],Term)
      stripNegation tm =
          case destNegation tm of
            Just (n,t) -> (n : ns, b) where (ns,b) = stripNegation t
            Nothing -> ([],tm)

      -------------------------------------------------------------------------
      -- Numerals
      -------------------------------------------------------------------------

      fromNaturals :: Set Name
      fromNaturals = Set.fromList
          [Const.fromNaturalRealName]

      destFromNatural :: Term -> Maybe Term
      destFromNatural tm = do
          (c,t) <- Term.destUnaryOp tm
          guard (Set.member (Const.name c) fromNaturals)
          return t

      destMaybeFromNatural :: Term -> Term
      destMaybeFromNatural tm =
          case destFromNatural tm of
            Just t -> t
            Nothing -> tm

      isZero :: Term -> Bool
      isZero tm =
          case Term.destConst tm of
            Just (c,_) -> Const.name c == Const.zeroName
            Nothing -> False

      destBit :: Term -> Maybe (Bool,Term)
      destBit tm = do
          (c,t) <- Term.destUnaryOp tm
          fmap (flip (,) t) $ bit (Const.name c)
        where
          bit n = if n == Const.bit0Name then Just False
                  else if n == Const.bit1Name then Just True
                  else Nothing

      destBits :: Term -> Maybe Integer
      destBits tm =
          if isZero tm then Just 0
          else do
            (b,t) <- destBit tm
            i <- destNumeral t
            bit b i
        where
          bit False 0 = Nothing
          bit b i = Just (2 * i + (if b then 1 else 0))

      destNumeral :: Term -> Maybe Integer
      destNumeral = destBits . destMaybeFromNatural

      isNumeral :: Term -> Bool
      isNumeral = isJust . destNumeral

      -------------------------------------------------------------------------
      -- Function application
      -------------------------------------------------------------------------

      destGenApp :: Term -> Maybe (Term,Term)
      destGenApp tm = do
          guard (not $ isNumeral tm)
          guard (not $ isInfix tm)
          guard (not $ isNegation tm)
          guard (not $ isBinder tm)
          --guard (not $ isCase tm)
          Term.destApp tm

      stripGenApp :: Term -> (Term,[Term])
      stripGenApp =
          go []
        where
          go xs tm =
              case destGenApp tm of
                Nothing -> (tm,xs)
                Just (f,x) -> go (x : xs) f
