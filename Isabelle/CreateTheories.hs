{-# LANGUAGE CPP #-}
{- |
Module      :  $Header$
Description :  creating Isabelle thoeries via translations
Copyright   :  (c) C. Maeder, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

dumping a LibEnv to Isabelle theory files
-}

module Isabelle.CreateTheories where

import Common.Result
import Common.AS_Annotation
import Logic.Coerce
import Logic.Comorphism

import Static.GTheory
import Logic.Prover

import Common.ExtSign
import Common.ProofUtils
import Isabelle.IsaSign
import Isabelle.Translate
import Isabelle.Logic_Isabelle

import CASL.Logic_CASL
import HasCASL.Logic_HasCASL

import Comorphisms.CASL2PCFOL
import Comorphisms.CASL2HasCASL
import Comorphisms.PCoClTyConsHOL2PairsInIsaHOL
import Comorphisms.HasCASL2PCoClTyConsHOL
#ifdef PROGRAMATICA
import Comorphisms.Haskell2IsabelleHOLCF
import Haskell.Logic_Haskell
#endif

createIsaTheory :: G_theory -> Result (Sign, [Named Sentence])
createIsaTheory (G_theory lid (ExtSign sign0 _) _ sens0 _) = do
    let th = (sign0, toNamedList sens0)
        r1 = coerceBasicTheory lid CASL "" th
        r1' = do
          th0 <- r1
          th1 <- wrapMapTheory CASL2PCFOL th0
          th2 <- wrapMapTheory CASL2HasCASL th1
          wrapMapTheory PCoClTyConsHOL2PairsInIsaHOL th2
#ifdef PROGRAMATICA
        r2 = coerceBasicTheory lid Haskell "" th
        r2' = do
          th0 <- r2
          wrapMapTheory Haskell2IsabelleHOLCF th0
#else
        r2 = r1
        r2' = r1'
#endif
        r4 = coerceBasicTheory lid HasCASL "" th
        r4' = do
          th0 <- r4
          th1 <- wrapMapTheory HasCASL2PCoClTyConsHOL th0
          wrapMapTheory PCoClTyConsHOL2PairsInIsaHOL th1
        r5 = coerceBasicTheory lid Isabelle "" th
        r3 = case maybeResult r1 of
               Nothing -> case maybeResult r2 of
                   Nothing -> case maybeResult r4 of
                       Nothing -> r5
                       _ -> r4'
                   _ -> r2'
               _ -> r1'
    (sign, sens) <- r3
    return (sign, prepareSenNames transString $ toNamedList $ toThSens sens)
