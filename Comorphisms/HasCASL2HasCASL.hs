{-# LANGUAGE MultiParamTypeClasses #-}
{- |
Module      :  $Header$
Description :  translating executable formulas to programs
Copyright   :  (c) Christian Maeder, Uni Bremen 2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

translate HasCASL formulas to HasCASL program equations
-}

module Comorphisms.HasCASL2HasCASL where

import Logic.Logic
import Logic.Comorphism

import HasCASL.Logic_HasCASL
import HasCASL.Sublogic
import HasCASL.As
import HasCASL.Le
import HasCASL.ProgEq

import qualified Data.Set as Set
import Common.AS_Annotation

-- | The identity of the comorphism
data HasCASL2HasCASL = HasCASL2HasCASL deriving Show

instance Language HasCASL2HasCASL where
  language_name HasCASL2HasCASL = "HasCASL2HasCASLPrograms"

instance Comorphism HasCASL2HasCASL
               HasCASL Sublogic
               BasicSpec Sentence SymbItems SymbMapItems
               Env Morphism Symbol RawSymbol ()
               HasCASL Sublogic
               BasicSpec Sentence SymbItems SymbMapItems
               Env Morphism Symbol RawSymbol () where
    sourceLogic HasCASL2HasCASL = HasCASL
    sourceSublogic HasCASL2HasCASL = top
    targetLogic HasCASL2HasCASL = HasCASL
    mapSublogic HasCASL2HasCASL = Just . id
    map_morphism HasCASL2HasCASL = return
    map_sentence HasCASL2HasCASL env = return . translateSen env
    map_symbol HasCASL2HasCASL _ = Set.singleton
    map_theory HasCASL2HasCASL (sig, sen) = return
      (sig, map  (mapNamed (translateSen sig)) sen)
