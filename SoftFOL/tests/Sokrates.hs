{- |
Module      :  $Header$
Copyright   :  (c) Rene Wagner, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rwagner@informatik.uni-bremen.de
Stability   :  provisional
Portability :  unknown

The Sokrates example from the SPASS tutorial at
<http://spass.mpi-sb.mpg.de/tutorial/> as a Haskell data structure.

-}

import SoftFOL.Sign

import Common.AS_Annotation

main = return () -- to allow for make SoftFOL/tests/Sokrates.o

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
    f1 = NamedSen { senAttr  = "f1",
                    isAxiom  = True,
                    sentence = SPComplexTerm {symbol= SPCustomSymbol "Human",
                                              arguments= [SPSimpleTerm (SPCustomSymbol "sokrates")] } }
    f2 = NamedSen { senAttr  = "f2",
                    isAxiom  = True,
                    sentence = SPQuantTerm {quantSym= SPForall, 
                                            variableList= [SPSimpleTerm (SPCustomSymbol "x")],
                                            qFormula= SPComplexTerm { symbol= SPImplies,
                                                                      arguments= [SPComplexTerm {symbol= SPCustomSymbol "Human", arguments= [SPSimpleTerm (SPCustomSymbol "x")]},
                                                                                  SPComplexTerm {symbol= SPCustomSymbol "Mortal", arguments= [SPSimpleTerm (SPCustomSymbol "x")]}] } } }

sokratesConjectureFormulae :: SPFormulaList
sokratesConjectureFormulae = SPFormulaList { originType= SPOriginConjectures,
                                             formulae= [f3] }
  where
    f3 = NamedSen { senAttr  = "f3",
                    isAxiom  = False,
                    sentence = SPComplexTerm {symbol= SPCustomSymbol "Mortal",
                                              arguments= [SPSimpleTerm (SPCustomSymbol "sokrates")] } }
