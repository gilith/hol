{- |
module: $Header$
description: Higher order logic conversions
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.Conv
where

import HOL.Data
import qualified HOL.Rule as Rule
import qualified HOL.Term as Term
import qualified HOL.TermAlpha as TermAlpha
import HOL.Thm (Thm)
import qualified HOL.Thm as Thm

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

data Result =
    Unchanged
  | Changed Thm
  deriving (Eq,Ord,Show)

newtype Conv = Conv (Term -> Maybe Result)

-------------------------------------------------------------------------------
-- Applying conversions to terms
-------------------------------------------------------------------------------

apply :: Conv -> Term -> Maybe Result
apply (Conv f) tm = f tm

applyData :: Conv -> Conv -> Conv -> TermData -> Maybe Result
applyData cf cx _ (AppTerm f x) = do
    f' <- apply cf f
    x' <- apply cx x
    case (f',x') of
      (Unchanged,Unchanged) -> return Unchanged
      (Unchanged, Changed x'') -> return $ Changed $ Rule.randUnsafe f x''
      (Changed f'', Unchanged) -> return $ Changed $ Rule.ratorUnsafe f'' x
      (Changed f'', Changed x'') -> return $ Changed $ Thm.mkAppUnsafe f'' x''
applyData _ _ cb (AbsTerm v b) = do
    b' <- apply cb b
    case b' of
      Unchanged -> return Unchanged
      Changed b'' -> return $ Changed $ Thm.mkAbsUnsafe v b''
applyData _ _ _ _ = Just Unchanged

applyTerm :: Conv -> Term -> Term
applyTerm c tm =
    case apply c tm of
      Just (Changed th) -> Term.rhsUnsafe $ TermAlpha.dest $ Thm.concl $ th
      _ -> tm

-------------------------------------------------------------------------------
-- Basic conversions
-------------------------------------------------------------------------------

fail :: Conv
fail = Conv (const Nothing)

id :: Conv
id = Conv (const $ Just Unchanged)

beta :: Conv
beta = Conv (fmap Changed . Thm.betaConv)

-------------------------------------------------------------------------------
-- Conversionals
-------------------------------------------------------------------------------

orelse :: Conv -> Conv -> Conv
orelse c1 c2 = Conv f
  where
    f tm = case apply c1 tm of
             Nothing -> apply c2 tm
             x -> x

thenc :: Conv -> Conv -> Conv
thenc c1 c2 = Conv f
  where
    f tm = let r1 = apply c1 tm in
           case r1 of
             Nothing -> Nothing
             Just Unchanged -> apply c2 tm
             Just (Changed th1) ->
                 let tm' = Term.rhsUnsafe $ TermAlpha.dest $ Thm.concl th1 in
                 case apply c2 tm' of
                   Nothing -> Nothing
                   Just Unchanged -> r1
                   Just (Changed th2) ->
                       Just $ Changed $ Rule.transUnsafe th1 th2

try :: Conv -> Conv
try c = c `orelse` HOL.Conv.id

repeat :: Conv -> Conv
repeat c = try (c `thenc` HOL.Conv.repeat c)

sub :: Conv -> Conv
sub c = Conv (applyData c c c . Term.dest)

rator :: Conv -> Conv
rator c = Conv (applyData c HOL.Conv.id HOL.Conv.id . Term.dest)

rand :: Conv -> Conv
rand c = Conv (applyData HOL.Conv.id c HOL.Conv.id . Term.dest)

abs :: Conv -> Conv
abs c = Conv (applyData HOL.Conv.id HOL.Conv.id c . Term.dest)

-------------------------------------------------------------------------------
-- Traversal strategies
-------------------------------------------------------------------------------

bottomUp :: Conv -> Conv
bottomUp c = sub (bottomUp c) `thenc` try c

-------------------------------------------------------------------------------
-- Evaluating terms to weak head normal form
-------------------------------------------------------------------------------

eval :: Conv -> Conv
eval c = whnf
  where
    whnf = rator whnf `thenc` try ((c `orelse` beta) `thenc` whnf)
