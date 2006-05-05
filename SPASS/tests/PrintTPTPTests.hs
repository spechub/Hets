import SPASS.Sign
import SPASS.PrintTPTP

import Common.AS_Annotation
import Common.Lib.Pretty


-- | a more pretty alternative for shows using PrintTPTP
showPretty2 :: PrintTPTP a => a -> ShowS
showPretty2 = shows . printTPTP


main :: IO ()
main = do
  putStr "--- Term-Tests ---\n"
  putStr $ showPretty2 spSimpleTermTest1 "\n\n"
  putStr $ showPretty2 spQuantTermTest1 "\n\n"
  putStr $ showPretty2 spQuantTermTest2 "\n\n"
  putStr $ showPretty2 spQuantTermTest3 "\n\n"
  putStr $ showPretty2 spQuantTermTest4 "\n\n"
  putStr $ showPretty2 spQuantTermTest5 "\n\n"
  
  putStr "--- Formula-Test ---\n"
  putStr $ render $ printFormula SPOriginAxioms spFormulaTest
  putStr "\n\n"
  
  putStr "--- FormulaList-Tests ---\n"
  putStr $ showPretty2 spFormulaListTest1 "\n\n"
  putStr $ showPretty2 spFormulaListTest2 "\n\n"
  putStr $ showPretty2 spFormulaListTest3 "\n\n"
  putStr $ showPretty2 spFormulaListTest4 "\n\n"
  
  putStr "--- Description-Tests ---\n"
  putStr $ showPretty2 spDescTest1 "\n\n"
  putStr $ showPretty2 spDescTest2 "\n\n"
  
  putStr "--- Problem-Test ---\n"
  putStr $ showPretty2 spProblemTest "\n"
  return ()
  

spSimpleTermTest1 :: SPSymbol
spSimpleTermTest1 = SPCustomSymbol "testsymbol"

spQuantTermTest1 :: SPTerm
spQuantTermTest1 = SPQuantTerm {quantSym= SPForall, termTermList= [SPSimpleTerm (SPCustomSymbol "a")], termTerm= SPComplexTerm {symbol= SPEqual, arguments= [SPSimpleTerm (SPCustomSymbol "a"), SPSimpleTerm (SPCustomSymbol "a")]}}

spQuantTermTest2 :: SPTerm
spQuantTermTest2 = SPQuantTerm {quantSym= SPForall, termTermList= [SPSimpleTerm (SPCustomSymbol "a"), SPSimpleTerm (SPCustomSymbol "b")], termTerm= SPComplexTerm {symbol= SPEqual, arguments= [
  SPComplexTerm {symbol=SPCustomSymbol "Elem", arguments=[SPSimpleTerm (SPCustomSymbol "a")]},
  SPComplexTerm {symbol=SPCustomSymbol "Elem", arguments=[SPSimpleTerm (SPCustomSymbol "b")]}
]}}

spQuantTermTest3 :: SPTerm
spQuantTermTest3 = SPQuantTerm {quantSym= SPExists, termTermList= [SPComplexTerm {symbol=SPCustomSymbol "Klein", arguments=[SPSimpleTerm (SPCustomSymbol "pi")]}, SPComplexTerm {symbol=SPCustomSymbol "Elem", arguments=[SPSimpleTerm (SPCustomSymbol "y")]}],
termTerm= SPComplexTerm {symbol= SPEqual, arguments= [SPSimpleTerm (SPCustomSymbol "pi"), SPSimpleTerm (SPCustomSymbol "y")]}}

spQuantTermTest4 :: SPTerm
spQuantTermTest4 = SPQuantTerm {quantSym= SPForall, termTermList= [
 SPComplexTerm {symbol=SPCustomSymbol "Elem", arguments=[SPSimpleTerm (SPCustomSymbol "y")]},
 SPComplexTerm {symbol=SPCustomSymbol "Elem", arguments=[SPSimpleTerm (SPCustomSymbol "a"), SPSimpleTerm (SPCustomSymbol "b"), SPSimpleTerm (SPCustomSymbol "c")]}
],
termTerm= SPComplexTerm {symbol= SPOr, arguments= [
 SPComplexTerm {symbol=SPCustomSymbol "Elem", arguments=[SPSimpleTerm (SPCustomSymbol "y")]},
 SPComplexTerm {symbol=SPCustomSymbol "Elem", arguments=[SPSimpleTerm (SPCustomSymbol "a"), SPSimpleTerm (SPCustomSymbol "b"), SPSimpleTerm (SPCustomSymbol "c")]}
]}}

spQuantTermTest5 :: SPTerm
spQuantTermTest5 = SPQuantTerm {quantSym= SPCustomQuantSym "T", termTermList = [
 SPComplexTerm {symbol=SPCustomSymbol "Elem", arguments=[SPSimpleTerm (SPCustomSymbol "y")]},
 SPComplexTerm {symbol=SPCustomSymbol "Elem", arguments=[SPSimpleTerm (SPCustomSymbol "a"), SPSimpleTerm (SPCustomSymbol "b"), SPSimpleTerm (SPCustomSymbol "c")]},
 SPComplexTerm {symbol=SPNot, arguments=[SPSimpleTerm (SPCustomSymbol "blue")]}
],
termTerm=
SPComplexTerm {symbol=SPEqual, arguments=[
  SPComplexTerm {symbol= SPOr, arguments=[
    SPComplexTerm {symbol=SPCustomSymbol "Elem", arguments=[SPSimpleTerm (SPCustomSymbol "y")]},
    SPComplexTerm {symbol=SPNot, arguments=[SPSimpleTerm (SPCustomSymbol "blue")]}
  ]},
  SPComplexTerm {symbol=SPCustomSymbol "Elem", arguments=[SPSimpleTerm (SPCustomSymbol "a"), SPSimpleTerm (SPCustomSymbol "b"), SPSimpleTerm (SPCustomSymbol "c")]}
]}}
 
spFormulaTest :: SPFormula
spFormulaTest = (emptyName SPComplexTerm {symbol= SPEqual, arguments= [SPSimpleTerm (SPCustomSymbol "a"), SPSimpleTerm (SPCustomSymbol "a")]}) {senName= "testformula"}

spFormulaListTest1 :: SPFormulaList
spFormulaListTest1 = SPFormulaList {originType= SPOriginAxioms, formulae= [(emptyName SPComplexTerm {symbol= SPEqual, arguments= [SPSimpleTerm (SPCustomSymbol "a"), SPSimpleTerm (SPCustomSymbol "a")]}) {senName= "testformula"}]}

spFormulaListTest2 :: SPFormulaList
spFormulaListTest2 = SPFormulaList {originType= SPOriginConjectures, formulae= [(emptyName SPComplexTerm {symbol= SPEqual, arguments= [SPSimpleTerm (SPCustomSymbol "a"), SPSimpleTerm (SPCustomSymbol "a")]}) {senName= "testformula"}]}

spFormulaListTest3 :: SPFormulaList
spFormulaListTest3 = SPFormulaList {originType= SPOriginAxioms, formulae= [(emptyName SPComplexTerm {symbol= SPEqual, arguments= [SPSimpleTerm (SPCustomSymbol "a"), SPSimpleTerm (SPCustomSymbol "a")]}) {senName= "testformula"}, (emptyName SPComplexTerm {symbol= SPEqual, arguments= [SPSimpleTerm (SPCustomSymbol "a"), SPSimpleTerm (SPCustomSymbol "a")]}) {senName= "testformula"}]}

spFormulaListTest4 :: SPFormulaList
spFormulaListTest4 = SPFormulaList {originType= SPOriginConjectures, formulae= [(emptyName SPComplexTerm {symbol= SPEqual, arguments= [SPSimpleTerm (SPCustomSymbol "a"), SPSimpleTerm (SPCustomSymbol "a")]}){senName= "testformula"}, (emptyName SPComplexTerm {symbol= SPEqual, arguments= [SPSimpleTerm (SPCustomSymbol "a"), SPSimpleTerm (SPCustomSymbol "a")]}) {senName= "testformula"}]}


spDescTest1 :: SPDescription
spDescTest1 = SPDescription {name="testdesc", author="testauthor", version=Nothing, logic=Nothing, status=SPStateUnknown, desc="Just a test.", date=Nothing}

spDescTest2 :: SPDescription
spDescTest2 = SPDescription {name="testdesc", author="testauthor", version=Just "0.1", logic=Just "logic description", status=SPStateUnknown, desc="Just a test.", date=Just "today"}

spProblemTest :: SPProblem
spProblemTest = SPProblem {identifier= "testproblem", description= descr, logicalPart= logical_part, settings= []}
  where
  descr = SPDescription {name="testdesc", author="testauthor", version=Nothing, logic=Nothing, status=SPStateUnknown, desc="Just a test.", date=Nothing}
  logical_part = SPLogicalPart {symbolList= Nothing, declarationList= [], formulaLists= [SPFormulaList {originType= SPOriginAxioms, formulae= [(emptyName SPComplexTerm {symbol= SPEqual, arguments= [SPSimpleTerm (SPCustomSymbol "a"), SPSimpleTerm (SPCustomSymbol "a")]}) {senName= "testformula"}]},SPFormulaList {originType= SPOriginConjectures, formulae= [(emptyName SPComplexTerm {symbol= SPEqual, arguments= [SPSimpleTerm (SPCustomSymbol "a"), SPSimpleTerm (SPCustomSymbol "a")]}) {senName= "testformula"}, (emptyName SPComplexTerm {symbol= SPEqual, arguments= [SPSimpleTerm (SPCustomSymbol "a"), SPSimpleTerm (SPCustomSymbol "a")]}) {senName= "testformula"}]}]}

