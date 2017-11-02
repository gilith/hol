{- |
module: $Header$
description: Higher order logic substitutions
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.Subst
where

import Control.Monad (guard)
import Control.Monad.Trans.State (State,get,put,evalState)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe,isNothing)
import Data.Set (Set)
import qualified Data.Set as Set

import HOL.Data
import qualified HOL.Term as Term
import HOL.TypeSubst (TypeSubst)
import qualified HOL.TypeSubst as TypeSubst
import HOL.Util (mkUnsafe2)
import qualified HOL.Var as Var

-------------------------------------------------------------------------------
-- Capture-avoiding substitutions
-------------------------------------------------------------------------------

data Subst = Subst TypeSubst (Map Var Term) (Map Term (Maybe Term))

-------------------------------------------------------------------------------
-- Constructors and destructors
-------------------------------------------------------------------------------

mk :: TypeSubst -> Map Var Term -> Maybe Subst
mk ts m = do
    guard (all (uncurry Term.sameTypeVar) $ Map.toList m)
    return $ Subst ts (Map.filterWithKey norm m) Map.empty
  where
    norm v tm = not $ Term.eqVar v tm

mkUnsafe :: TypeSubst -> Map Var Term -> Subst
mkUnsafe = mkUnsafe2 "HOL.Subst.mk" mk

dest :: Subst -> (TypeSubst, Map Var Term)
dest (Subst ts m _) = (ts,m)

fromList :: [(TypeVar,Type)] -> [(Var,Term)] -> Maybe Subst
fromList ts = mk (TypeSubst.fromList ts) . Map.fromList

fromListUnsafe :: [(TypeVar,Type)] -> [(Var,Term)] -> Subst
fromListUnsafe = mkUnsafe2 "HOL.Subst.fromList" fromList

empty :: Subst
empty = Subst TypeSubst.empty Map.empty Map.empty

singleton :: Var -> Term -> Maybe Subst
singleton v tm = fromList [] [(v,tm)]

singletonUnsafe :: Var -> Term -> Subst
singletonUnsafe = mkUnsafe2 "HOL.Subst.singleton" singleton

null :: Subst -> Bool
null (Subst ts m _) = TypeSubst.null ts && Map.null m

-------------------------------------------------------------------------------
-- Avoiding capture
-------------------------------------------------------------------------------

capturableVars :: Var -> Term -> Term -> Set Var
capturableVars v =
    \tm tm' -> evalState (termVars tm tm') Set.empty
  where
    noVars :: Set Var
    noVars = Set.empty

    termVars :: Term -> Term -> State (Set (Term,Term)) (Set Var)
    termVars tm tm' =
        if Var.notFreeIn v tm then return $ Var.free tm'
        else cachedIdem subVars noVars (tm,tm')

    subVars :: (Term,Term) -> State (Set (Term,Term)) (Set Var)
    subVars (tm,tm') = dataVars (Term.dest tm) (Term.dest tm')

    dataVars :: TermData -> TermData -> State (Set (Term,Term)) (Set Var)
    dataVars (VarTerm _) _ = return noVars  -- must be variable v
    dataVars (AppTerm f x) (AppTerm f' x') = do
        fv <- termVars f f'
        xv <- termVars x x'
        return $ Set.union fv xv
    dataVars (AbsTerm _ b) (AbsTerm v' b') = do  -- cannot be variable v
        bv <- termVars b b'
        return $ Set.insert v' bv
    dataVars _ _ = error "HOL.Subst.capturableVars.dataVars"

    cachedIdem :: Ord a => (a -> State (Set a) b) -> b ->
                  a -> State (Set a) b
    cachedIdem f i a = do
      s <- get
      case Set.member a s of
        True -> return i
        False -> do
          b <- f a
          s' <- get
          put (Set.insert a s')
          return b

renameBoundVar :: Var -> Term -> Term -> Term -> Term
renameBoundVar v v' =
    \tm tm' -> evalState (termRename tm tm') Map.empty
  where
    termRename :: Term -> Term -> State (Map (Term,Term) Term) Term
    termRename tm tm' =
        if Var.notFreeIn v tm then return tm'
        else cached subRename (tm,tm')

    subRename :: (Term,Term) -> State (Map (Term,Term) Term) Term
    subRename (tm,tm') = dataRename (Term.dest tm) (Term.dest tm')

    dataRename :: TermData -> TermData -> State (Map (Term,Term) Term) Term
    dataRename (VarTerm _) _ = return v' -- must be variable v
    dataRename (AppTerm f x) (AppTerm f' x') = do
        f'' <- termRename f f'
        x'' <- termRename x x'
        return $ Term.mkAppUnsafe f'' x''
    dataRename (AbsTerm _ b) (AbsTerm w' b') = do  -- cannot be variable v
        b'' <- termRename b b'
        return $ Term.mkAbs w' b''
    dataRename _ _ = error "HOL.Subst.renameBoundVar.dataRename"

    cached :: Ord a => (a -> State (Map a b) b) -> a -> State (Map a b) b
    cached f a = do
      c <- get
      case Map.lookup a c of
        Just b -> return b
        Nothing -> do
          b <- f a
          c' <- get
          put (Map.insert a b c')
          return b

avoidCapture :: Bool -> Var -> Var -> Term -> Term -> (Var,Term)
avoidCapture vSub' v v' b b' =
    (v'',b'')
  where
    avoid = Set.map Var.name $ capturableVars v b b'
    v'' = Var.renameAvoiding avoid v'
    b'' = if not vSub' && v'' == v' then b'
          else renameBoundVar v (Term.mkVar v'') b b'

-------------------------------------------------------------------------------
-- Primitive substitutions
-------------------------------------------------------------------------------

varSubst :: Var -> Subst -> (Maybe Term, Subst)
varSubst v s =
    (tm,s')
  where
    -- first apply the type substitution
    (v',s') = basicSubst v s
    -- then apply the term substitution
    tm = case v' of
           Nothing -> Map.lookup v m
           Just w -> Just $ fromMaybe (Term.mkVar w) (Map.lookup w m)
    Subst _ m _ = s'

dataSubst :: TermData -> Subst -> (Maybe Term, Subst)
dataSubst (ConstTerm c ty) s =
    (fmap (Term.mkConst c) ty', s')
  where
    (ty',s') = basicSubst ty s
dataSubst (VarTerm v) s = varSubst v s
dataSubst (AppTerm f x) s =
    (tm',s'')
  where
    (f',s') = basicSubst f s
    (x',s'') = basicSubst x s'
    tm' = case f' of
            Nothing -> fmap (Term.mkAppUnsafe f) x'
            Just g -> Just (Term.mkAppUnsafe g $ fromMaybe x x')
dataSubst (AbsTerm v b) s =
    (tm',s'')
  where
    (v',s') = basicSubst v s
    (b',s'') = basicSubst b s'
    tm' = if isNothing v' && isNothing b' then Nothing
          else Just (Term.mkAbs v'' b'')
    (v'',b'') = avoidCapture wSub v w b (fromMaybe b b')
    wSub = Map.member w m where Subst _ m _ = s''
    w = fromMaybe v v'

-------------------------------------------------------------------------------
-- General substitutions
-------------------------------------------------------------------------------

class CanSubst a where
  --
  -- This is the primitive substitution function for types to implement,
  -- which has the following properties:
  --  1. Can assume the substitution is not null
  --  2. Returns Nothing if the argument is unchanged by the substitution
  --  3. Returns the substitution with updated type and term caches
  --
  basicSubst :: a -> Subst -> (Maybe a, Subst)

  --
  -- These substitution functions return Nothing if unchanged
  --
  sharingSubst :: a -> Subst -> (Maybe a, Subst)
  sharingSubst x s = if HOL.Subst.null s then (Nothing,s) else basicSubst x s

  subst :: Subst -> a -> Maybe a
  subst s x = fst $ sharingSubst x s

  typeSubst :: TypeSubst -> a -> Maybe a
  typeSubst ts = subst $ mkUnsafe ts Map.empty

  --
  -- These substitution functions return their argument if unchanged
  --
  trySharingSubst :: a -> Subst -> (a,Subst)
  trySharingSubst x s = (fromMaybe x x', s') where (x',s') = sharingSubst x s

  trySubst :: Subst -> a -> a
  trySubst s x = fromMaybe x (subst s x)

  tryTypeSubst :: TypeSubst -> a -> a
  tryTypeSubst ts x = fromMaybe x (typeSubst ts x)

instance CanSubst a => CanSubst [a] where
  basicSubst [] s = (Nothing,s)
  basicSubst (h : t) s =
      (l',s'')
    where
      (h',s') = basicSubst h s
      (t',s'') = basicSubst t s'
      l' = case h' of
             Nothing -> fmap ((:) h) t'
             Just x -> Just (x : fromMaybe t t')

instance (Ord a, CanSubst a) => CanSubst (Set a) where
  basicSubst xs s =
      (xs',s')
    where
      xl = Set.toList xs
      (xl',s') = basicSubst xl s
      xs' = fmap Set.fromList xl'

instance CanSubst Type where
  basicSubst ty s =
      (ty', Subst ts' m c)
    where
      Subst ts m c = s
      (ty',ts') = TypeSubst.sharingSubst ty ts

-- This only applies the type substitution
instance CanSubst Var where
  basicSubst (Var n ty) s =
      (fmap (Var n) ty', s')
    where
      (ty',s') = basicSubst ty s

instance CanSubst Term where
  basicSubst tm s =
      case Map.lookup tm c of
        Just tm' -> (tm',s)
        Nothing ->
            (tm', Subst ts m (Map.insert tm tm' c'))
          where
            (tm', Subst ts m c') = dataSubst (Term.dest tm) s
    where
      Subst _ _ c = s
