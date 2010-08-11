{- |
Module      :  $Header$
Description :  creating Haskell modules via translations
Copyright   :  (c) C. Maeder, Uni Bremen 2006
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

dumping a LibEnv to a Haskell module
-}

module Haskell.CreateModules where

import Common.Result
import Common.ExtSign
import Common.Doc

import Logic.Coerce
import Logic.Logic
import Logic.Comorphism
import Static.GTheory
import Logic.Prover

import CASL.Logic_CASL
import HasCASL.Logic_HasCASL
import Haskell.Logic_Haskell

import Comorphisms.HasCASL2Haskell
import Comorphisms.CASL2HasCASL
import Comorphisms.HasCASL2HasCASL

printModule :: G_theory -> Maybe Doc
printModule (G_theory lid (ExtSign sign0 _) _ sens0 _) =
                let th = (sign0, toNamedList sens0)
                    r1 = do
                      th0 <- coerceBasicTheory lid CASL "" th
                      th1 <- wrapMapTheory CASL2HasCASL th0
                      th2 <- wrapMapTheory HasCASL2HasCASL th1
                      wrapMapTheory HasCASL2Haskell th2
                    r2 = do
                      th0 <- coerceBasicTheory lid HasCASL "" th
                      th2 <- wrapMapTheory HasCASL2HasCASL th0
                      wrapMapTheory HasCASL2Haskell th2
                    r3 = case maybeResult r1 of
                         Nothing -> r2
                         _ -> r1
                in case maybeResult r3 of
                   Nothing -> Nothing
                   Just (_, sens) -> Just $
                       vcat $ map (print_named Haskell) sens
