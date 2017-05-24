{- |
module: $Header$
description: Higher order logic theories
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.Theory
where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import qualified HOL.Const as Const
import HOL.Data
import HOL.Name
import HOL.Sequent (Sequent)
import HOL.Thm (Thm)
import qualified HOL.Thm as Thm
import qualified HOL.TypeOp as TypeOp

-------------------------------------------------------------------------------
-- Theories
-------------------------------------------------------------------------------

data Theory =
    Theory
      {typeOpMap :: Map Name (Set TypeOp),
       constMap :: Map Name (Set Const),
       thmMap :: Map Sequent Thm}
  deriving (Eq,Ord,Show)

-------------------------------------------------------------------------------
-- Constructors and destructors
-------------------------------------------------------------------------------

empty :: Theory
empty = Theory {typeOpMap = Map.empty, constMap = Map.empty, thmMap = Map.empty}

fromThmSet :: Set Thm -> Theory
fromThmSet ths =
    Theory {typeOpMap = t, constMap = c, thmMap = th}
  where
    mkSingle k v x = Map.singleton (k x) (v x)
    mkGen k v u = Map.unionsWith u . map (mkSingle k v) . Set.toList
    mkSet k = mkGen k Set.singleton Set.union
    mkSimple k = mkGen k id const

    t = mkSet TypeOp.name $ TypeOp.ops ths
    c = mkSet Const.name $ Const.consts ths
    th = mkSimple Thm.dest ths

-------------------------------------------------------------------------------
-- Union
-------------------------------------------------------------------------------

union :: Theory -> Theory -> Theory
union thy1 thy2 =
    Theory {typeOpMap = t, constMap = c, thmMap = th}
  where
    Theory {typeOpMap = t1, constMap = c1, thmMap = th1} = thy1
    Theory {typeOpMap = t2, constMap = c2, thmMap = th2} = thy2

    t = Map.unionWith Set.union t1 t2
    c = Map.unionWith Set.union c1 c2
    th = Map.union th1 th2

unionList :: [Theory] -> Theory
unionList = foldr union empty

-------------------------------------------------------------------------------
-- Type operators
-------------------------------------------------------------------------------

instance TypeOp.HasOps Theory where
  ops = TypeOp.ops . Map.elems . typeOpMap

lookupTypeOp :: Theory -> Name -> Maybe TypeOp
lookupTypeOp thy n =
    case Map.lookup n $ typeOpMap thy of
      Nothing -> Just $ TypeOp.mkUndef n
      Just s -> if Set.size s == 1 then Just (Set.findMin s) else Nothing

-------------------------------------------------------------------------------
-- Constants
-------------------------------------------------------------------------------

instance Const.HasConsts Theory where
  consts = Const.consts . Map.elems . constMap

lookupConst :: Theory -> Name -> Maybe Const
lookupConst thy n =
    case Map.lookup n $ constMap thy of
      Nothing -> Just $ Const.mkUndef n
      Just s -> if Set.size s == 1 then Just (Set.findMin s) else Nothing

-------------------------------------------------------------------------------
-- Theorems
-------------------------------------------------------------------------------

sequents :: Theory -> Set Sequent
sequents = Map.keysSet . thmMap

thms :: Theory -> Set Thm
thms = Set.fromList . Map.elems . thmMap

lookupThm :: Theory -> Sequent -> Maybe Thm
lookupThm thy sq = Map.lookup sq $ thmMap thy

-------------------------------------------------------------------------------
-- A minimal theory containing the standard axioms
-------------------------------------------------------------------------------

standard :: Theory
standard = fromThmSet Thm.standardAxioms
