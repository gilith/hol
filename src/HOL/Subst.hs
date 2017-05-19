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
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe,isNothing)
import Data.Set (Set)
import qualified Data.Set as Set

import HOL.Data
import qualified HOL.Term as Term
import HOL.TypeSubst (TypeSubst)
import qualified HOL.TypeSubst as TypeSubst
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
mkUnsafe ts m =
    case mk ts m of
      Just s -> s
      Nothing -> error "HOL.Subst.mk failed"

dest :: Subst -> (TypeSubst, Map Var Term)
dest (Subst ts m _) = (ts,m)

fromList :: [(TypeVar,Type)] -> [(Var,Term)] -> Maybe Subst
fromList ts = mk (TypeSubst.fromList ts) . Map.fromList

fromListUnsafe :: [(TypeVar,Type)] -> [(Var,Term)] -> Subst
fromListUnsafe ts l =
    case fromList ts l of
      Just s -> s
      Nothing -> error "HOL.Subst.fromList failed"

empty :: Subst
empty = Subst TypeSubst.empty Map.empty Map.empty

singleton :: Var -> Term -> Maybe Subst
singleton v tm = fromList [] [(v,tm)]

singletonUnsafe :: Var -> Term -> Subst
singletonUnsafe v tm =
    case singleton v tm of
      Just s -> s
      Nothing -> error "HOL.Subst.singleton failed"

null :: Subst -> Bool
null (Subst ts m _) = TypeSubst.null ts && Map.null m

-------------------------------------------------------------------------------
-- Avoiding capture
-------------------------------------------------------------------------------

capturableVars :: Var -> Term -> Term -> Set Var
capturableVars v =
    termVars
  where
    termVars :: Term -> Term -> Set Var
    termVars tm tm' =
        if Var.notFreeIn v tm then Var.free tm'
        else dataVars (Term.dest tm) (Term.dest tm')

    dataVars :: TermData -> TermData -> Set Var
    dataVars (VarTerm _) _ = Set.empty  -- must be variable v
    dataVars (AppTerm f x) (AppTerm f' x') =
        Set.union (termVars f f') (termVars x x')
    dataVars (AbsTerm _ b) (AbsTerm v' b') =  -- cannot be variable v
        Set.insert v' (termVars b b')
    dataVars _ _ = error "HOL.Subst.capturableVars.dataVars"

renameBoundVar :: Var -> Term -> Term -> Term -> Term
renameBoundVar v v' =
    \tm tm' -> fst $ termRename tm tm' Map.empty
  where
    termRename :: Term -> Term -> Map (Term,Term) Term ->
                  (Term, Map (Term,Term) Term)
    termRename tm tm' cache =
        case Map.lookup (tm,tm') cache of
          Just cached -> (cached,cache)
          Nothing -> (tm'', Map.insert (tm,tm') tm'' cache')
      where
        (tm'',cache') =
          if Var.notFreeIn v tm then (tm',cache)
          else dataRename (Term.dest tm) (Term.dest tm') cache

    dataRename :: TermData -> TermData -> Map (Term,Term) Term ->
                  (Term, Map (Term,Term) Term)
    dataRename (VarTerm _) _ cache =  -- must be variable v
        (v',cache)
    dataRename (AppTerm f x) (AppTerm f' x') cache =
        (Term.mkAppUnsafe f'' x'', cache'')
      where
        (f'',cache') = termRename f f' cache
        (x'',cache'') = termRename x x' cache'
    dataRename (AbsTerm _ b) (AbsTerm w' b') cache =  -- cannot be variable v
        (Term.mkAbs w' b'', cache')
      where
        (b'',cache') = termRename b b' cache
    dataRename _ _ _ = error "HOL.Subst.renameBoundVar.dataRename"

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
