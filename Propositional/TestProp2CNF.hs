{- |
Module      :  $Header$
Description :  Instance of class Logic for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

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

import Propositional.Prop2CNF -- FIXME: What happened to Prop2CNF?
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
aId = stringToId "a"

bId :: Id
bId = stringToId "b"

cId :: Id
cId = stringToId "c"

mySig :: Sign
mySig = addToSig (addToSig (addToSig emptySig aId) bId) cId


myForm :: FORMULA
myForm = Disjunction [Predication (mkSimpleId "a"),
          Negation (Predication (mkSimpleId "a")) nullRange]
          nullRange


myOtherForm :: FORMULA
myOtherForm = Conjunction [Equivalence (Predication (mkSimpleId "a"))
                        (Predication (mkSimpleId "c"))
                        nullRange] nullRange

{-
myForm :: FORMULA
myForm = (Predication (mkSimpleId "a"))
-}

myEmptyForm = makeNamed "myForm" myForm

otherForm = makeNamed "myOtherForm" myOtherForm

myForms = [myEmptyForm, otherForm]

runAll = translateToCNF (mySig, [myEmptyForm])

showStuff :: IO String
showStuff = PC.showDIMACSProblem "Problem " mySig myForms []

showProof = PC.goalDIMACSProblem "DIMACSProblem"
            (propProverState mySig myForms [])
            otherForm []
