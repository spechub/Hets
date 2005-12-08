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
import Common.PrettyPrint
import Common.Result
import Common.Lib.Pretty

import Logic.Coerce
import Logic.Comorphism

import Syntax.AS_Library
import Syntax.Print_AS_Library()

import Static.DevGraph
import Logic.Prover

import Common.ProofUtils
import Isabelle.IsaPrint
import Isabelle.Translate

import CASL.Logic_CASL
import HasCASL.Logic_HasCASL

import Comorphisms.CASL2PCFOL
import Comorphisms.PCFOL2CFOL
import Comorphisms.CFOL2IsabelleHOL
import Comorphisms.HasCASL2IsabelleHOL
#ifdef PROGRAMATICA
import Comorphisms.Haskell2IsabelleHOLCF
import Haskell.Logic_Haskell
#endif

printTheory :: String -> LIB_NAME -> SIMPLE_ID -> G_theory -> Maybe Doc
printTheory libdir ln sn (G_theory lid sign0 sens0) =
                let th = (sign0, toNamedList sens0)
                    r1 = do
                      th0 <- coerceBasicTheory lid CASL "" th
                      th1 <- map_theory CASL2PCFOL th0
                      th2 <- map_theory PCFOL2CFOL th1
                      map_theory CFOL2IsabelleHOL th2
#ifdef PROGRAMATICA
                    r2 = do
                      th0 <- coerceBasicTheory lid Haskell "" th
                      map_theory Haskell2IsabelleHOLCF th0
#else
                    r2 = r1
#endif
                    r4 = do
                      th0 <- coerceBasicTheory lid HasCASL "" th
                      map_theory HasCASL2IsabelleHOL th0
                    r3 = case maybeResult r1 of
                         Nothing -> case maybeResult r2 of
                             Nothing -> r4
                             _ -> r2
                         _ -> r1
                in case maybeResult r3 of
                   Nothing -> Nothing
                   Just (sign, sens) -> let
                     tn = reverse (takeWhile (/= '/') $ reverse $ show ln)
                          ++ "_" ++ showPretty sn ""
                     in Just $ printIsaTheory tn libdir sign
                        $ prepareSenNames transString
                              $ toNamedList $ toThSens sens
