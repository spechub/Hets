{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

   
   translate HasCASL formulas to HasCASL program equations

-}

module Comorphisms.HasCASL2HasCASL where

import Logic.Logic
import Logic.Comorphism

import HasCASL.Logic_HasCASL
import HasCASL.As
import HasCASL.Le
import HasCASL.Morphism
import HasCASL.ProgEq

import Common.Lib.Set
import Common.AS_Annotation

-- | The identity of the comorphism
data HasCASL2HasCASL = HasCASL2HasCASL deriving Show

instance Language HasCASL2HasCASL -- default definition is okay

instance Comorphism HasCASL2HasCASL
               HasCASL HasCASL_Sublogics
               BasicSpec Sentence SymbItems SymbMapItems
               Env Morphism Symbol RawSymbol ()
               HasCASL HasCASL_Sublogics
               BasicSpec Sentence SymbItems SymbMapItems
               Env Morphism Symbol RawSymbol () where
    sourceLogic HasCASL2HasCASL = HasCASL
    sourceSublogic HasCASL2HasCASL = top
    targetLogic HasCASL2HasCASL = HasCASL
    targetSublogic HasCASL2HasCASL = top
    map_morphism HasCASL2HasCASL = Just
    map_sentence HasCASL2HasCASL env = Just . translateSen env
    map_symbol HasCASL2HasCASL = single 
    map_theory HasCASL2HasCASL (sig, sen) = Just 
      (sig, map  (mapNamed (translateSen sig)) sen)

