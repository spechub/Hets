{- |
Module      :  $Header$
Description :  Instance of class Logic for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Test cases for Prop2CNF
-}

{-
  Ref.

  http://en.wikipedia.org/wiki/Propositional_logic

  Till Mossakowski, Joseph Goguen, Razvan Diaconescu, Andrzej Tarlecki.
  What is a Logic?.
  In Jean-Yves Beziau (Ed.), Logica Universalis, pp. 113-@133. Birkhaeuser.
  2005.
-}

module Propositional.TestProp2CNF
    where

import Propositional.Prop2CNF
import Propositional.AS_BASIC_Propositional
import Propositional.Sign
import Common.Id
import Common.AS_Annotation
import qualified SoftFOL.ProverState as PState
import qualified Propositional.Conversions as PC
import Propositional.Prove
import Propositional.ProverState
import qualified SoftFOL.Sign as SPS

aId :: Id
aId = simpleIdToId $ mkSimpleId "a"

bId :: Id
bId = simpleIdToId $ mkSimpleId "b"

cId :: Id
cId = simpleIdToId $ mkSimpleId "c"

mySig :: Sign
mySig = addToSig (addToSig (addToSig emptySig aId) bId) cId


myForm :: FORMULA
myForm = (Disjunction [(Predication (mkSimpleId "a")),
          Negation (Predication (mkSimpleId "a")) nullRange]
          nullRange)


myOtherForm :: FORMULA
myOtherForm = Conjunction [(Equivalence (Predication (mkSimpleId "a"))
                        (Predication (mkSimpleId "c"))
                        nullRange)
                     ] nullRange

{-
myForm :: FORMULA
myForm = (Predication (mkSimpleId "a"))
-}

myEmptyForm = [SenAttr
               {
                 senAttr = "myForm"
               , isAxiom = True
               , isDef   = False
               , wasTheorem = False
               , sentence = myForm
               }
              ]

myForms = [SenAttr
           {
             senAttr = "myForm"
           , isAxiom = True
           , isDef   = False
           , wasTheorem = False
           , sentence = myForm
           }
          ,SenAttr
           {
             senAttr = "myOtherForm"
           , isAxiom = True
           , isDef   = False
           , wasTheorem = False
           , sentence = myOtherForm
           }
          ]

runAll    = show $ translateToCNF (mySig, myEmptyForm)

showStuff = PC.ioDIMACSProblem "Problem " mySig myForms []

showProof = PC.goalDIMACSProblem "DIMACSProblem" (propProverState mySig myForms)
            SenAttr
            {
              senAttr = "myOtherForm"
            , isAxiom = True
            , isDef   = False
            , wasTheorem = False
            , sentence = myOtherForm
            }
            []
