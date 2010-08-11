{- |
Module      :  $Header$
Copyright   :  (c) Rene Wagner, Uni Bremen 2005
License     :  GPLv2 or higher

Maintainer  :  rwagner@informatik.uni-bremen.de
Stability   :  provisional
Portability :  unknown

The Sokrates example from the SPASS tutorial at
<http://spass.mpi-sb.mpg.de/tutorial/> as a Haskell data structure.
-}

import SoftFOL.Sign
import SoftFOL.Print ()
import Common.DocUtils
import Common.AS_Annotation
import Common.Id

main :: IO ()
main = putStrLn $ showDoc sokratesProblem ""

sokratesProblem :: SPProblem
sokratesProblem = SPProblem
  { identifier = "Sokrates1",
    description = sokratesDescription,
    logicalPart = sokratesLogicalPart,
    settings = [] }

sokratesDescription :: SPDescription
sokratesDescription = SPDescription
  { name = "Sokrates",
    author = "Christoph Weidenbach",
    version = Nothing,
    logic = Nothing,
    status = SPStateUnsatisfiable,
    desc =
    "Sokrates is mortal and since all humans are mortal, he is mortal too.",
    date = Nothing }

sokratesLogicalPart :: SPLogicalPart
sokratesLogicalPart = emptySPLogicalPart
  { symbolList = Just sokratesSymbolList,
    formulaLists = [sokratesAxiomFormulae, sokratesConjectureFormulae] }

sokratesSymbolList :: SPSymbolList
sokratesSymbolList = SPSymbolList
  { functions = [SPSignSym {sym= mkSimpleId "sokrates", arity= 0}],
    predicates = [SPSignSym {sym= mkSimpleId "Human", arity= 1}
                 , SPSignSym {sym= mkSimpleId "Mortal", arity= 1}],
    sorts= [] }

sokratesAxiomFormulae :: SPFormulaList
sokratesAxiomFormulae = SPFormulaList {originType= SPOriginAxioms,
                                       formulae= [f1, f2] }
  where
    f1 = makeNamed "f1" $ compTerm (mkSPCustomSymbol "Human")
         [ simpTerm $ mkSPCustomSymbol "sokrates"]
    f2 = makeNamed "f2" $ SPQuantTerm
         {quantSym= SPForall,
          variableList= [simpTerm (mkSPCustomSymbol "x")],
          qFormula= compTerm SPImplies
                 [ compTerm (mkSPCustomSymbol "Human")
                   [simpTerm $ mkSPCustomSymbol "x"]
                 , compTerm (mkSPCustomSymbol "Mortal")
                   [simpTerm $ mkSPCustomSymbol "x"]]}

sokratesConjectureFormulae :: SPFormulaList
sokratesConjectureFormulae = SPFormulaList
  { originType= SPOriginConjectures,
    formulae= [f3 {isAxiom  = False} ] }
  where
    f3 = makeNamed "f3" $ compTerm (mkSPCustomSymbol "Mortal")
         [simpTerm $ mkSPCustomSymbol "sokrates"]
