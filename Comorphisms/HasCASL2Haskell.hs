{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2004
Licence     :  All rights reserved.

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

   
   The embedding comorphism from HasCASL to Haskell.

-}

module Comorphisms.HasCASL2Haskell where

import Logic.Logic
import Logic.Comorphism

import HasCASL.Logic_HasCASL
import HasCASL.As
import HasCASL.Le
import HasCASL.Morphism

import Haskell.Logic_Haskell
import Haskell.HatParser
import Haskell.Hatchet.MultiModuleBasics 
import Haskell.Hatchet.AnnotatedHsSyn

import ToHaskell.FromHasCASL

-- | The identity of the comorphism
data HasCASL2Haskell = HasCASL2Haskell deriving Show

instance Language HasCASL2Haskell -- default definition is okay

instance Comorphism HasCASL2Haskell
               HasCASL ()
               BasicSpec Sentence SymbItems SymbMapItems
               Env
               Morphism
               Symbol RawSymbol ()
               Haskell ()
               HsDecls AHsDecl () ()
               ModuleInfo
               ()
               () () () where
    sourceLogic _ = HasCASL
    sourceSublogic _ = ()
    targetLogic _ = Haskell
    targetSublogic _ = ()
    map_sign _ = Just . mapSignature
    --map_morphism _ morphism1 -> Maybe morphism2
    map_sentence _ = mapSingleSentence
    --map_symbol :: cid -> symbol1 -> Set symbol2
    map_theory _ = Just . mapTheory

