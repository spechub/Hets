{- |
Module      :  ./OWL2/CreateOWL.hs
Description :  translate theories to OWL2
Copyright   :  (c) C. Maeder, DFKI GmbH 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (via Logic.Logic)
-}


module OWL2.CreateOWL where

import Common.Result
import Common.AS_Annotation
import Logic.Coerce
import Logic.Comorphism

import Static.GTheory
import Logic.Prover

import Common.ExtSign

import OWL2.Sign
import OWL2.MS
import qualified OWL2.AS as AS
import OWL2.Logic_OWL2
import OWL2.CASL2OWL
import OWL2.DMU2OWL2
import OWL2.Propositional2OWL2

import CASL.Logic_CASL
import ExtModal.Logic_ExtModal
import Comorphisms.ExtModal2OWL

import DMU.Logic_DMU
import Propositional.Logic_Propositional


createOWLTheory :: G_theory -> Result (Sign, [Named AS.Axiom])
createOWLTheory (G_theory lid _ (ExtSign sign0 _) _ sens0 _) = do
    let th = (sign0, toNamedList sens0)
        r1 = coerceBasicTheory lid CASL "" th
        r1' = r1 >>= wrapMapTheory CASL2OWL
    --     r2 = coerceBasicTheory lid DMU "" th
    --     r2' = r2 >>= wrapMapTheory DMU2OWL2
    --     r3 = coerceBasicTheory lid Propositional "" th
    --     r3' = r3 >>= wrapMapTheory Propositional2OWL2
        r4 = coerceBasicTheory lid ExtModal "" th
        r4' = r4 >>= wrapMapTheory ExtModal2OWL
    --     r5 = coerceBasicTheory lid OWL2 "" th
        r6 = case maybeResult r1 of
    --            Nothing -> case maybeResult r2 of
    --              Nothing -> case maybeResult r3 of
    --                Nothing -> case maybeResult r4 of
    --                  Nothing -> r5
    --                  _ -> r4'
    --                _ -> r3'
    --              _ -> r2'
               Nothing -> r4'
               _ -> r1'

    (sign, sens) <- r6
    return (sign, toNamedList $ toThSens sens)

    return (emptySign, [])
