{- |
Module      :  $Header$
Description :  Instance of class Logic for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@tzi.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Test cases for Prop2CNF
-}

{-
  Ref.

  http://en.wikipedia.org/wiki/Propositional_logic

  Till Mossakowski, Joseph Goguen, Razvan Diaconescu, Andrzej Tarlecki.
  What is a Logic?.
  In Jean-Yves Beziau (Ed.), Logica Universalis, pp. 113-@133. Birkhäuser.
  2005.
-}

module Propositional.TestProp2CNF
    where

import Propositional.Prop2CNF
import Propositional.AS_BASIC_Propositional
import Propositional.Sign
import Common.Id
import Common.AS_Annotation
import qualified SPASS.ProverState as PState

aId :: Id
aId = simpleIdToId $ mkSimpleId "a"

bId :: Id
bId = simpleIdToId $ mkSimpleId "b"

cId :: Id
cId = simpleIdToId $ mkSimpleId "c"

mySig :: Sign
mySig = addToSig (addToSig (addToSig emptySig aId) bId) cId


myForm :: FORMULA
myForm = Conjunction [(Implication (Predication (mkSimpleId "a")) 
                       (Predication (mkSimpleId "b"))
                       nullRange), Predication (mkSimpleId "a")
                     ] nullRange 

myOtherForm :: FORMULA
myOtherForm = Conjunction [(Equivalence (Predication (mkSimpleId "a"))
                        (Predication (mkSimpleId "c"))
                        nullRange)
                     ] nullRange 

{-
myForm :: FORMULA
myForm = (Predication (mkSimpleId "a"))
-}

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

myProverState :: PState.SPASSProverState
myProverState = createInitProverState mySig myForms

showMyForm :: IO String
showMyForm = showDFGProblem "Translation" myProverState [] 

myRun = runSpass myProverState True

runTranslation = show $ runSPASSandParseDFG myProverState True

runFull        = show $ translateProblem $ runSPASSandParseDFG myProverState True

runAll         = show $ translateToCNF (mySig, myForms)
