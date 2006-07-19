{-# OPTIONS -cpp #-}
{- |
Module      :  $Header$
Copyright   :  (c) C. Maeder, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  paolot@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

dumping a LibEnv to Isabelle theory files
-}

module Isabelle.CreateTheories where

import Common.Id
import Common.Result
import Common.Doc
import Logic.Coerce
import Logic.Comorphism

import Syntax.AS_Library

import Static.DevGraph
import Logic.Prover

import Common.ProofUtils
import Isabelle.IsaPrint
import Isabelle.Translate
import Isabelle.Logic_Isabelle

import CASL.Logic_CASL
import HasCASL.Logic_HasCASL

import Comorphisms.CASL2PCFOL
import Comorphisms.CASL2SubCFOL
import Comorphisms.CFOL2IsabelleHOL
import Comorphisms.PCoClTyConsHOL2IsabelleHOL
#ifdef PROGRAMATICA
import Comorphisms.Haskell2IsabelleHOLCF
import Haskell.Logic_Haskell
#endif

printTheory :: String -> LIB_NAME -> SIMPLE_ID -> G_theory -> Result Doc
printTheory libdir ln sn (G_theory lid sign0 sens0) = do
    let th = (sign0, toNamedList sens0)
        r1 = coerceBasicTheory lid CASL "" th
        r1' = do
          th0 <- r1
          th1 <- wrapMapTheory CASL2PCFOL th0
          th2 <- wrapMapTheory CASL2SubCFOL th1
          wrapMapTheory CFOL2IsabelleHOL th2
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
          wrapMapTheory PCoClTyConsHOL2IsabelleHOL th0
        r5 = coerceBasicTheory lid Isabelle "" th
        r3 = case maybeResult r1 of
               Nothing -> case maybeResult r2 of
                   Nothing -> case maybeResult r4 of
                       Nothing -> r5
                       _ -> r4'
                   _ -> r2'
               _ -> r1'
    (sign, sens) <- r3 
    let tn = reverse (takeWhile (/= '/') 
                     $ reverse $ show $ getLIB_ID ln)
             ++ "_" ++ tokStr sn
    return $ printIsaTheory tn libdir sign
               $ prepareSenNames transString
               $ toNamedList $ toThSens sens
