{- |
Module      :  $Header$
Copyright   :  (c) Rene Wagner, Uni Bremen 2005
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  rwagner@tzi.de
Stability   :  provisional
Portability :  unknown

   The Sokrates example from the SPASS tutorial at
   <http://spass.mpi-sb.mpg.de/tutorial/> as a Haskell data structure.

-}

import SPASS.Sign
import SPASS.Print

import Common.AS_Annotation
import Common.PrettyPrint
import Common.Lib.Pretty

sokratesProblem :: SPProblem
sokratesProblem = SPProblem { identifier = "Sokrates1",
                              description = sokratesDescription,
                              logicalPart = sokratesLogicalPart }

sokratesDescription :: SPDescription
sokratesDescription = SPDescription { name = "Sokrates",
                                      author = "Christoph Weidenbach",
                                      version = Nothing,
                                      logic = Nothing,
                                      status = SPStateUnsatisfiable,
                                      desc = "Sokrates is mortal and since all humans are mortal, he is mortal too.",
                                      date = Nothing }

sokratesLogicalPart :: SPLogicalPart
sokratesLogicalPart = SPLogicalPart { symbolList = Just sokratesSymbolList,
                                      declarationList = [],
                                      formulaLists = [sokratesAxiomFormulae, sokratesConjectureFormulae] }

sokratesSymbolList :: SPSymbolList
sokratesSymbolList = SPSymbolList { functions = [SPSignSym {sym= "sokrates", arity= 0}],
                                    predicates = [SPSignSym {sym= "Human", arity= 1}, SPSignSym {sym= "Mortal", arity= 1}],
                                    sorts= [],
                                    operators= [],
                                    quantifiers= [] }

sokratesAxiomFormulae :: SPFormulaList
sokratesAxiomFormulae = SPFormulaList {originType= SPOriginAxioms,
                                       formulae= [f1, f2] }
  where
    f1 = SPFormula {formulaLabel = "1",
                    formulaTerm  = SPComplexTerm {symbol= SPCustomSymbol "Human",
                                                  arguments= [SPSimpleTerm (SPCustomSymbol "sokrates")] } }
    f2 = SPFormula {formulaLabel = "2",
                   formulaTerm   = SPQuantTerm {quantSym= SPForall, 
                                                termTermList= [SPSimpleTerm (SPCustomSymbol "x")],
                                                termTerm= SPComplexTerm { symbol= SPImplies,
                                                                          arguments= [SPComplexTerm {symbol= SPCustomSymbol "Human", arguments= [SPSimpleTerm (SPCustomSymbol "x")]},
                                                                                      SPComplexTerm {symbol= SPCustomSymbol "Mortal", arguments= [SPSimpleTerm (SPCustomSymbol "x")]}] } } }

sokratesConjectureFormulae :: SPFormulaList
sokratesConjectureFormulae = SPFormulaList { originType= SPOriginConjectures,
                                             formulae= [f3] }
  where
    f3 = SPFormula {formulaLabel = "3",
                    formulaTerm  = SPComplexTerm {symbol= SPCustomSymbol "Mortal",
                                                  arguments= [SPSimpleTerm (SPCustomSymbol "sokrates")] } }
