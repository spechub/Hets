{- |
Module      :  ./SoftFOL/tests/PrintTPTPTests.hs
Copyright   :  (c) C. Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

-}

module Main where

import SoftFOL.Sign
import SoftFOL.PrintTPTP

import Common.AS_Annotation
import Common.Id


-- | a more pretty alternative for shows using PrintTPTP
showPretty2 :: PrintTPTP a => a -> ShowS
showPretty2 = shows . printTPTP


main :: IO ()
main = do
  putStrLn "--- Term-Tests ---"
  putStrLn $ showPretty2 spSimpleTermTest1 "\n"
  putStrLn $ showPretty2 spQuantTermTest1 "\n"
  putStrLn $ showPretty2 spQuantTermTest2 "\n"
  putStrLn $ showPretty2 spQuantTermTest3 "\n"
  putStrLn $ showPretty2 spQuantTermTest4 "\n"
  putStrLn $ showPretty2 spQuantTermTest5 "\n"

  putStrLn "--- Formula-Test ---"
  print $ printFormula SPOriginAxioms spFormulaTest
  putStrLn "\n"

  putStrLn "--- FormulaList-Tests ---"
  putStrLn $ showPretty2 spFormulaListTest1 "\n"
  putStrLn $ showPretty2 spFormulaListTest2 "\n"
  putStrLn $ showPretty2 spFormulaListTest3 "\n"
  putStrLn $ showPretty2 spFormulaListTest4 "\n"

  putStrLn "--- Description-Tests ---"
  putStrLn $ showPretty2 spDescTest1 "\n"
  putStrLn $ showPretty2 spDescTest2 "\n"

  putStrLn "--- Problem-Test ---"
  putStrLn $ showPretty2 spProblemTest "\n"

  putStrLn "--- Declaration-Test ---"
  putStrLn $ showPretty2 spDeclTest "\n"

spSimpleTermTest1 :: SPSymbol
spSimpleTermTest1 = mkSPCustomSymbol "testsymbol"

spQuantTermTest1 :: SPTerm
spQuantTermTest1 = SPQuantTerm {quantSym = SPForall, variableList = [simpTerm (mkSPCustomSymbol "a")], qFormula = SPComplexTerm {symbol = SPEqual, arguments = [simpTerm (mkSPCustomSymbol "a"), simpTerm (mkSPCustomSymbol "a")]}}

spQuantTermTest2 :: SPTerm
spQuantTermTest2 = SPQuantTerm {quantSym = SPForall, variableList = [simpTerm (mkSPCustomSymbol "a"), simpTerm (mkSPCustomSymbol "b")], qFormula = SPComplexTerm {symbol = SPEqual, arguments = [
  SPComplexTerm {symbol = mkSPCustomSymbol "Elem", arguments = [simpTerm (mkSPCustomSymbol "a")]},
  SPComplexTerm {symbol = mkSPCustomSymbol "Elem", arguments = [simpTerm (mkSPCustomSymbol "b")]}
]}}

spQuantTermTest3 :: SPTerm
spQuantTermTest3 = SPQuantTerm {quantSym = SPExists, variableList = [SPComplexTerm {symbol = mkSPCustomSymbol "Klein", arguments = [simpTerm (mkSPCustomSymbol "pi")]}, SPComplexTerm {symbol = mkSPCustomSymbol "Elem", arguments = [simpTerm (mkSPCustomSymbol "y")]}],
qFormula = SPComplexTerm {symbol = SPEqual, arguments = [simpTerm (mkSPCustomSymbol "pi"), simpTerm (mkSPCustomSymbol "y")]}}

spQuantTermTest4 :: SPTerm
spQuantTermTest4 = SPQuantTerm {quantSym = SPForall, variableList = [
 SPComplexTerm {symbol = mkSPCustomSymbol "Elem", arguments = [simpTerm (mkSPCustomSymbol "y")]},
 SPComplexTerm {symbol = mkSPCustomSymbol "Elem", arguments = [simpTerm (mkSPCustomSymbol "a"), simpTerm (mkSPCustomSymbol "b"), simpTerm (mkSPCustomSymbol "c")]}
],
qFormula = SPComplexTerm {symbol = SPOr, arguments = [
 SPComplexTerm {symbol = mkSPCustomSymbol "Elem", arguments = [simpTerm (mkSPCustomSymbol "y")]},
 SPComplexTerm {symbol = mkSPCustomSymbol "Elem", arguments = [simpTerm (mkSPCustomSymbol "a"), simpTerm (mkSPCustomSymbol "b"), simpTerm (mkSPCustomSymbol "c")]}
]}}

spQuantTermTest5 :: SPTerm
spQuantTermTest5 = SPQuantTerm {quantSym = SPCustomQuantSym $ mkSimpleId "T", variableList = [
 SPComplexTerm {symbol = mkSPCustomSymbol "Elem", arguments = [simpTerm (mkSPCustomSymbol "y")]},
 SPComplexTerm {symbol = mkSPCustomSymbol "Elem", arguments = [simpTerm (mkSPCustomSymbol "a"), simpTerm (mkSPCustomSymbol "b"), simpTerm (mkSPCustomSymbol "c")]},
 SPComplexTerm {symbol = SPNot, arguments = [simpTerm (mkSPCustomSymbol "blue")]}
],
qFormula =
SPComplexTerm {symbol = SPEqual, arguments = [
  SPComplexTerm {symbol = SPOr, arguments = [
    SPComplexTerm {symbol = mkSPCustomSymbol "Elem", arguments = [simpTerm (mkSPCustomSymbol "y")]},
    SPComplexTerm {symbol = SPNot, arguments = [simpTerm (mkSPCustomSymbol "blue")]}
  ]},
  SPComplexTerm {symbol = mkSPCustomSymbol "Elem", arguments = [simpTerm (mkSPCustomSymbol "a"), simpTerm (mkSPCustomSymbol "b"), simpTerm (mkSPCustomSymbol "c")]}
]}}

toTestFormula :: SPTerm -> SPFormula
toTestFormula = makeNamed "testFormula"

spFormulaTest :: SPFormula
spFormulaTest = toTestFormula SPComplexTerm {symbol = SPEqual, arguments = [simpTerm (mkSPCustomSymbol "a"), simpTerm (mkSPCustomSymbol "a")]}

spFormulaListTest1 :: SPFormulaList
spFormulaListTest1 = SPFormulaList {originType = SPOriginAxioms, formulae = [toTestFormula SPComplexTerm {symbol = SPEqual, arguments = [simpTerm (mkSPCustomSymbol "a"), simpTerm (mkSPCustomSymbol "a")]}]}

spFormulaListTest2 :: SPFormulaList
spFormulaListTest2 = SPFormulaList {originType = SPOriginConjectures, formulae = [toTestFormula SPComplexTerm {symbol = SPEqual, arguments = [simpTerm (mkSPCustomSymbol "a"), simpTerm (mkSPCustomSymbol "a")]}]}

spFormulaListTest3 :: SPFormulaList
spFormulaListTest3 = SPFormulaList {originType = SPOriginAxioms, formulae = [toTestFormula SPComplexTerm {symbol = SPEqual, arguments = [simpTerm (mkSPCustomSymbol "a"), simpTerm (mkSPCustomSymbol "a")]}, toTestFormula SPComplexTerm {symbol = SPEqual, arguments = [simpTerm (mkSPCustomSymbol "a"), simpTerm (mkSPCustomSymbol "a")]}]}

spFormulaListTest4 :: SPFormulaList
spFormulaListTest4 = SPFormulaList {originType = SPOriginConjectures, formulae = [toTestFormula SPComplexTerm {symbol = SPEqual, arguments = [simpTerm (mkSPCustomSymbol "a"), simpTerm (mkSPCustomSymbol "a")]}, toTestFormula SPComplexTerm {symbol = SPEqual, arguments = [simpTerm (mkSPCustomSymbol "a"), simpTerm (mkSPCustomSymbol "a")]}]}


spDescTest1 :: SPDescription
spDescTest1 = SPDescription {name = "testdesc", author = "testauthor", version = Nothing, logic = Nothing, status = SPStateUnknown, desc = "Just a test.", date = Nothing}

spDescTest2 :: SPDescription
spDescTest2 = SPDescription {name = "testdesc", author = "testauthor", version = Just "0.1", logic = Just "logic description", status = SPStateUnknown, desc = "Just a test.", date = Just "today"}

spProblemTest :: SPProblem
spProblemTest = SPProblem {identifier = "testproblem", description = descr, logicalPart = logical_part, settings = []}
  where
  descr = SPDescription {name = "testdesc", author = "testauthor", version = Nothing, logic = Nothing, status = SPStateUnknown, desc = "Just a test.", date = Nothing}
  logical_part = emptySPLogicalPart {
    declarationList = Just [spDeclTest, spDeclTest2],
    formulaLists = [SPFormulaList {originType = SPOriginAxioms, formulae = [toTestFormula SPComplexTerm {symbol = SPEqual, arguments = [simpTerm (mkSPCustomSymbol "a"), simpTerm (mkSPCustomSymbol "a")]}]}, SPFormulaList {originType = SPOriginConjectures, formulae = [toTestFormula SPComplexTerm {symbol = SPEqual, arguments = [simpTerm (mkSPCustomSymbol "a"), simpTerm (mkSPCustomSymbol "a")]}, toTestFormula SPComplexTerm {symbol = SPEqual, arguments = [simpTerm (mkSPCustomSymbol "a"), simpTerm (mkSPCustomSymbol "a")]}]}]}

spDeclTest :: SPDeclaration
spDeclTest = SPSubsortDecl
  { sortSymA = mkSimpleId "sortSymA"
  , sortSymB = mkSimpleId "sortSymB" }

spDeclTest2 :: SPDeclaration
spDeclTest2 = SPTermDecl {termDeclTermList = [
 SPComplexTerm {symbol = mkSPCustomSymbol "Elem", arguments = [simpTerm (mkSPCustomSymbol "y")]},
 SPComplexTerm {symbol = mkSPCustomSymbol "Elem", arguments = [simpTerm (mkSPCustomSymbol "a"), simpTerm (mkSPCustomSymbol "b"), simpTerm (mkSPCustomSymbol "c")]}
],
termDeclTerm = SPComplexTerm {symbol = SPOr, arguments = [
 SPComplexTerm {symbol = mkSPCustomSymbol "Elem", arguments = [simpTerm (mkSPCustomSymbol "y")]},
 SPComplexTerm {symbol = mkSPCustomSymbol "Elem", arguments = [simpTerm (mkSPCustomSymbol "a"), simpTerm (mkSPCustomSymbol "b"), simpTerm (mkSPCustomSymbol "c")]}
]}}
