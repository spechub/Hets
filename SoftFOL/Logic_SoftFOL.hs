{-# LANGUAGE CPP, MultiParamTypeClasses, TypeSynonymInstances
  , FlexibleInstances #-}
{- |
Module      :  ./SoftFOL/Logic_SoftFOL.hs
Description :  Instance of class Logic for SoftFOL.
Copyright   :  (c) Rene Wagner, Klaus Luettich, Uni Bremen 2005-2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic)

Instance of class Logic for SoftFOL.
-}

module SoftFOL.Logic_SoftFOL where

import Data.Set (toList)

import Common.DefaultMorphism
import Common.DocUtils
import Common.ProofTree

import ATC.ProofTree ()

import Logic.Logic

import SoftFOL.ATC_SoftFOL ()
import SoftFOL.Sign
import SoftFOL.StatAna
import SoftFOL.Print
import SoftFOL.Conversions
import SoftFOL.Morphism
import SoftFOL.PrintTPTP ()

import SoftFOL.ProveSPASS
import SoftFOL.ProveHyperHyper
#ifndef NOHTTP
import SoftFOL.ProveMathServ
import SoftFOL.ProveVampire
#endif
import SoftFOL.ProveDarwin
import SoftFOL.ProveMetis

instance Pretty Sign where
  pretty = pretty . signToSPLogicalPart

{- |
  A dummy datatype for the LogicGraph and for identifying the right
  instances
-}
data SoftFOL = SoftFOL deriving (Show)

instance Language SoftFOL where
 description _ =
  "SoftFOL - Softly typed First Order Logic for " ++
       "Automated Theorem Proving Systems\n\n" ++
  "This logic corresponds to the logic of SPASS, \n" ++
  "but the generation of TPTP is also possible.\n" ++
  "See http://spass.mpi-sb.mpg.de/\n" ++
  "and http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html"

instance Logic.Logic.Syntax SoftFOL [TPTP] SFSymbol () ()
    -- default implementation is fine!

instance Sentences SoftFOL Sentence Sign
                           SoftFOLMorphism SFSymbol where
      map_sen SoftFOL _ = return
      sym_of SoftFOL = singletonList . symOf
      symsOfSen SoftFOL sign = toList . symsOfTerm sign
      sym_name SoftFOL = symbolToId
      symKind SoftFOL = sfSymbKind . sym_type
      print_named SoftFOL = printFormula
      negation _ = negateSentence
    -- other default implementations are fine

instance StaticAnalysis SoftFOL [TPTP] Sentence
               () ()
               Sign
               SoftFOLMorphism SFSymbol () where
         empty_signature SoftFOL = emptySign
         is_subsig SoftFOL _ _ = True
         subsig_inclusion SoftFOL = defaultInclusion
         basic_analysis SoftFOL = Just basicAnalysis

instance Logic SoftFOL () [TPTP] Sentence () ()
               Sign
               SoftFOLMorphism SFSymbol () ProofTree where
         stability _ = Stable
         provers SoftFOL = [spassProver]
#ifndef NOHTTP
           ++ [mathServBroker, vampire]
#endif
           ++ map darwinProver tptpProvers
           ++ [metisProver, hyperProver]
         cons_checkers SoftFOL = map darwinConsChecker tptpProvers
           ++ [hyperConsChecker]
