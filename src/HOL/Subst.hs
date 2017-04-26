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

mk :: TypeSubst -> Map Var Term -> Subst
mk ts m =
    Subst ts (Map.filterWithKey norm m) Map.empty
  where
    norm v tm = not $ Term.equalVar v tm

dest :: Subst -> (TypeSubst, Map Var Term)
dest (Subst ts m _) = (ts,m)

fromList :: [(TypeVar,Type)] -> [(Var,Term)] -> Subst
fromList ts = mk (TypeSubst.fromList ts) . Map.fromList

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
    dataVars _ _ = error "bad arguments"

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
        case Term.mkApp f'' x'' of
          Just tm'' -> (tm'',cache'')
          Nothing -> error "bad types in mkApp"
      where
        (f'',cache') = termRename f f' cache
        (x'',cache'') = termRename x x' cache'
    dataRename (AbsTerm _ b) (AbsTerm w' b') cache =  -- cannot be variable v
        (Term.mkAbs w' b'', cache')
      where
        (b'',cache') = termRename b b' cache
    dataRename _ _ _ = error "dataRename: bad arguments"

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
    (v',s') = sharingSubst v s
    -- then apply the term substitution
    tm = case v' of
           Nothing -> Map.lookup v m
           Just w -> Just $ fromMaybe (Term.mkVar w) (Map.lookup w m)
    Subst _ m _ = s'

dataSubst :: TermData -> Subst -> (Maybe Term, Subst)
dataSubst (ConstTerm c ty) s =
    (fmap (Term.mkConst c) ty', s')
  where
    (ty',s') = sharingSubst ty s
dataSubst (VarTerm v) s = varSubst v s
dataSubst (AppTerm f x) s =
    (tm',s'')
  where
    (f',s') = sharingSubst f s
    (x',s'') = sharingSubst x s'
    tm' = case f' of
            Nothing -> fmap (app f) x'
            Just g -> Just (app g $ fromMaybe x x')
    app g y =
        case Term.mkApp g y of
          Just gy -> gy
          Nothing -> error "dataSubst: bad types in AppTerm"
dataSubst (AbsTerm v b) s =
    (tm',s'')
  where
    (v',s') = sharingSubst v s
    (b',s'') = sharingSubst b s'
    tm' = if isNothing v' && isNothing b' then Nothing
          else Just (Term.mkAbs v'' b'')
    (v'',b'') = avoidCapture wSub v w b (fromMaybe b b')
    wSub = Map.member w m where Subst _ m _ = s''
    w = fromMaybe v v'

-------------------------------------------------------------------------------
-- General substitutions
-------------------------------------------------------------------------------

class CanSubst a where
  -- these substitution functions return Nothing if unchanged
  sharingSubst :: a -> Subst -> (Maybe a, Subst)

  subst :: Subst -> a -> Maybe a
  subst s x = fst $ sharingSubst x s

  -- these substitution functions return their argument if unchanged
  trySharingSubst :: a -> Subst -> (a,Subst)
  trySharingSubst x s =
      (fromMaybe x y, s')
    where
      (y,s') = sharingSubst x s

  trySubst :: Subst -> a -> a
  trySubst s x = fromMaybe x (subst s x)

instance CanSubst a => CanSubst [a] where
  sharingSubst [] s = (Nothing,s)
  sharingSubst (h : t) s =
      (l',s'')
    where
      (h',s') = sharingSubst h s
      (t',s'') = sharingSubst t s'
      l' = case h' of
             Nothing -> fmap ((:) h) t'
             Just x -> Just (x : fromMaybe t t')

instance CanSubst Type where
  sharingSubst ty s =
      (ty', Subst ts' m c)
    where
      Subst ts m c = s
      (ty',ts') = TypeSubst.sharingSubst ty ts

-- this only applies the type substitution
instance CanSubst Var where
  sharingSubst (Var n ty) s =
      (fmap (Var n) ty', s')
    where
      (ty',s') = sharingSubst ty s

instance CanSubst Term where
  sharingSubst tm s =
      case Map.lookup tm c of
        Just tm' -> (tm',s)
        Nothing ->
            (tm', Subst ts m (Map.insert tm tm' c'))
          where
            (tm', Subst ts m c') = dataSubst (Term.dest tm) s
    where
      Subst _ _ c = s
