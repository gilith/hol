{- |
module: Main
description: Testing the higher order logic kernel
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}
module Main
  ( main )
where

import Data.List (sort)
import qualified Data.List as List
import Data.Set (Set)
import qualified Data.Set as Set
import System.FilePath ((</>),(<.>))
import Test.QuickCheck
import qualified Text.PrettyPrint as PP

import HOL.Name
import HOL.OpenTheory (readArticle)
import HOL.OpenTheory.Interpret (Interpret)
import qualified HOL.OpenTheory.Interpret as Interpret
import HOL.OpenTheory.Package (Package,readPackageFile)
import HOL.Parse
import HOL.Print
import qualified HOL.Rule as Rule
import qualified HOL.Subst as Subst
import qualified HOL.Term as Term
import qualified HOL.TermAlpha as TermAlpha
import HOL.Theory (Theory)
import qualified HOL.Theory as Theory
import HOL.Thm (Thm)
import qualified HOL.Thm as Thm
import qualified HOL.Type as Type
import qualified HOL.TypeSubst as TypeSubst
import qualified HOL.TypeVar as TypeVar
import qualified HOL.Var as Var

--------------------------------------------------------------------------------
-- Helper functions
--------------------------------------------------------------------------------

checkWith :: Testable prop => Args -> (String,prop) -> IO ()
checkWith args (desc,prop) =
    do putStr (desc ++ " ")
       res <- quickCheckWithResult args prop
       case res of
         Failure {} -> error "Proposition failed"
         _ -> return ()

{- No parametrized tests yet
check :: Testable prop => (String,prop) -> IO ()
check = checkWith $ stdArgs {maxSuccess = 1000}
-}

assert :: (String,Bool) -> IO ()
assert = checkWith $ stdArgs {maxSuccess = 1}

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

compareType :: (String,Bool)
compareType = ("Comparing types",prop)
  where
    prop = sort [a,b,i] == [a,b,i]

    a = Type.alpha
    b = Type.bool
    i = Type.ind

composeTypeSubst :: (String,Bool)
composeTypeSubst = ("Composing type substitutions",prop)
  where
    prop = TypeSubst.compose sub1 sub2 == sub12 &&
           subst sub12 alpha == subst sub2 (subst sub1 alpha)

    sub1 = TypeSubst.singleton TypeVar.alpha ty1
    ty1 = Type.mkFun Type.bool alpha

    sub2 = TypeSubst.singleton TypeVar.alpha ty2
    ty2 = Type.mkFun alpha Type.bool

    sub12 = TypeSubst.singleton TypeVar.alpha ty12
    ty12 = Type.mkFun Type.bool ty2

    subst = TypeSubst.trySubst
    alpha = Type.alpha

testTypes :: IO ()
testTypes = do
    assert compareType
    assert composeTypeSubst

--------------------------------------------------------------------------------
-- Terms
--------------------------------------------------------------------------------

compareTermAlpha :: (String,Bool)
compareTermAlpha = ("Comparing terms modulo alpha-equivalence",prop)
  where
    prop = --
           -- Comparing bound and free variables
           t1 < t2 && t2 < t3 && t3 < t4 &&
           a1 == a4 && a4 < a3 && a3 < a2 &&
           --
           -- Comparing bound variables by type
           t5 < t6 && t6 < t7 && t7 < t8 &&
           a7 == a8 && a8 < a5 && a5 < a6

    t1 = Term.mkAbs x (Term.mkVar x)
    t2 = Term.mkAbs x (Term.mkVar y)
    t3 = Term.mkAbs y (Term.mkVar x)
    t4 = Term.mkAbs y (Term.mkVar y)
    t5 = Term.mkAbs b t1
    t6 = Term.mkAbs i t1
    t7 = Term.mkAbs x t1
    t8 = Term.mkAbs y t1

    a1 = TermAlpha.mk t1
    a2 = TermAlpha.mk t2
    a3 = TermAlpha.mk t3
    a4 = TermAlpha.mk t4
    a5 = TermAlpha.mk t5
    a6 = TermAlpha.mk t6
    a7 = TermAlpha.mk t7
    a8 = TermAlpha.mk t8

    b = Var.mk (mkGlobal "b") Type.bool
    i = Var.mk (mkGlobal "i") Type.ind
    x = Var.mk (mkGlobal "x") Type.alpha
    y = Var.mk (mkGlobal "y") Type.alpha

substAvoidCapture :: (String,Bool)
substAvoidCapture = ("Term substitutions avoiding variable capture",prop)
  where
    prop = Subst.subst s1 t1 == Just t2 &&
           Subst.subst s2 t3 == Just t4 &&
           Subst.subst s2 t5 == Just t6

    s1 = Subst.singletonUnsafe p q'
    s2 = Subst.fromListUnsafe [(TypeVar.alpha,Type.bool)] []

    t1 = Term.mkAbs q (Term.mkEqUnsafe p' q')
    t2 = Term.mkAbs q0 (Term.mkEqUnsafe q' q0')
    t3 = Term.mkAbs qA (Term.mkEqUnsafe (Term.mkRefl q') (Term.mkRefl qA'))
    t4 = Term.mkAbs q0 (Term.mkEqUnsafe (Term.mkRefl q') (Term.mkRefl q0'))
    t5 = Term.mkAbs q (Term.mkEqUnsafe (Term.mkRefl q') (Term.mkRefl qA'))
    t6 = Term.mkAbs q0 (Term.mkEqUnsafe (Term.mkRefl q0') (Term.mkRefl q'))

    p' = Term.mkVar p
    q' = Term.mkVar q
    qA' = Term.mkVar qA
    q0' = Term.mkVar q0

    p = Var.mk (mkGlobal "p") Type.bool
    q = Var.mk (mkGlobal "q") Type.bool
    qA = Var.mk (mkGlobal "q") Type.alpha
    q0 = Var.mk (mkGlobal "q0") Type.bool

testTerms :: IO ()
testTerms = do
    assert compareTermAlpha
    assert substAvoidCapture

--------------------------------------------------------------------------------
-- Theorems
--------------------------------------------------------------------------------

inferenceRules :: (String,Bool)
inferenceRules = ("Rules of inference",prop)
  where
    prop = toString th1 == "|- (\\x. x) = \\x. x" &&
           toString th2 == "|- (\\a. abs (rep a)) = \\a. a" &&
           toString th3 == "|- (\\r. rep (abs r) = r) = \\r. (\\x. x) = r" &&
           toString th4 == "|- abs (rep a) = a" &&
           toString th5 == "|- (\\x. x) = r <=> rep (abs r) = r" &&
           toString th6 == "|- rep (abs r) = r <=> (\\x. x) = r"

    th1 = Thm.refl (Term.mkAbs x (Term.mkVar x))
    Just (_,_,_,th2,th3) = Thm.defineTypeOp unit absN rep [] th1
    Just (_,_,_,th4,th5) = Rule.defineTypeOpLegacy unit absN rep [] th1
    Just th6 = Rule.sym th5

    x = Var.mk (mkGlobal "x") Type.bool

    absN = mkGlobal "abs"
    rep = mkGlobal "rep"
    unit = mkGlobal "unit"

printedAxioms :: String
printedAxioms =
    separator ++ "\n" ++
    "Axiom of Extensionality\n" ++
    "\n" ++
    toStringWith style Thm.axiomOfExtensionality ++ "\n" ++
    "\n" ++
    separator ++ "\n" ++
    "Axiom of Choice\n" ++
    "\n" ++
    toStringWith style Thm.axiomOfChoice ++ "\n" ++
    "\n" ++
    separator ++ "\n" ++
    "Axiom of Infinity\n" ++
    "\n" ++
    toStringWith style Thm.axiomOfInfinity ++ "\n" ++
    "\n" ++
    separator ++ "\n"
  where
    lineLength = 160
    separator = replicate lineLength '-'
    style = PP.style {PP.lineLength = lineLength, PP.ribbonsPerLine = 2.0}

printAxioms :: String -> (String,Bool)
printAxioms ref = ("Printing axioms",prop)
  where
    prop = printedAxioms == ref

{- Use this to update the reference file
updatePrintedAxioms :: IO ()
updatePrintedAxioms = writeFile "doc/axioms.txt" printedAxioms
-}

testTheorems :: IO ()
testTheorems = do
    assert inferenceRules
    do --updatePrintedAxioms
       ref <- readFile axiomsFile
       assert $ printAxioms ref
  where
    axiomsFile = "doc" </> "axioms" <.> "txt"

--------------------------------------------------------------------------------
-- OpenTheory interpretations
--------------------------------------------------------------------------------

printedInterpret :: Interpret -> String
printedInterpret int =
    separator ++ "\n" ++
    "# Interpreting Boolean operator names into " ++
    "the OpenTheory standard namespace\n" ++
    separator ++ "\n" ++
    "\n" ++
    "# Data\n" ++
    "\n" ++
    "# Data.Bool\n" ++
    "\n" ++
    toString int ++ "\n"
  where
    separator = replicate 79 '#'

printInterpret :: String -> (String,Bool)
printInterpret ref = ("Parsing/printing interpretation",prop)
  where
    prop = case fromString ref of
             Nothing -> False
             Just int -> printedInterpret int == ref

{- Use this to normalize the interpretation file
updatePrintedInterpret :: IO ()
updatePrintedInterpret = do
    int <- fromTextFile "test/bool.int"
    writeFile "test/bool.int.new" $ printedInterpret int
-}

testInterpretations :: IO ()
testInterpretations = do
    --updatePrintedInterpret
    ref <- readFile boolIntFile
    assert $ printInterpret ref
    return ()
  where
    boolIntFile = "test" </> "bool" <.> "int"

--------------------------------------------------------------------------------
-- OpenTheory articles
--------------------------------------------------------------------------------

printedArticle :: Set Thm -> String
printedArticle ths =
    "Boolean operator definitions\n" ++
    "\n" ++
    List.intercalate "\n\n" (map toString $ Set.toList ths) ++ "\n"

printArticle :: String -> Set Thm -> (String,Bool)
printArticle ref ths = ("Summarizing article",prop)
  where
    prop = printedArticle ths == ref

{- Use this to update the reference file
updatePrintedArticle :: IO ()
updatePrintedArticle = do
    ths <- readArticle Theory.standard "test/bool.art"
    writeFile "doc/bool.txt" $ printedArticle ths
-}

testArticles :: IO (Set Thm)
testArticles = do
    --updatePrintedArticle
    ths <- readArticle Theory.standard Interpret.empty boolArtFile
    ref <- readFile boolTxtFile
    assert $ printArticle ref ths
    return ths
  where
    boolArtFile = "test" </> "bool-def" <.> "art"
    boolTxtFile = "doc" </> "bool" <.> "txt"

--------------------------------------------------------------------------------
-- OpenTheory packages
--------------------------------------------------------------------------------

printedPackage :: Package -> String
printedPackage thy = toString thy ++ "\n"

printPackage :: String -> (String,Bool)
printPackage ref = ("Parsing/printing package",prop)
  where
    prop = case fromString ref of
             Nothing -> False
             Just thy -> printedPackage thy == ref

checkPackageFile :: Set Thm -> Theory -> (String,Bool)
checkPackageFile ths thy = ("Reading a package file",prop)
  where
    prop = Theory.thms thy == ths

testPackages :: Set Thm -> IO ()
testPackages ths = do
    do ref <- readFile boolPkgFile
       assert $ printPackage ref
    do thy <- readPackageFile Theory.standard Interpret.empty boolPkgFile
       assert $ checkPackageFile ths thy
  where
    boolPkgFile = "test" </> "bool" <.> "thy"

--------------------------------------------------------------------------------
-- Main function
--------------------------------------------------------------------------------

main :: IO ()
main = do
    testTypes
    testTerms
    testTheorems
    testInterpretations
    ths <- testArticles
    testPackages ths
    return ()
