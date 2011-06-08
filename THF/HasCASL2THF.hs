{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  translation from HasCASL to THF
Copyright   :  (c) A. Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :
Stability   :
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from HasCASL to THF.
-}

-- TODO move this file from Hets/THF to Hets/Comorphisms

module Comorphisms.HasCASL2THF where

import Logic.Logic as Logic
import Logic.Comorphism

import HasCASL.Logic_HasCASL
import HasCASL.Sublogic
import HasCASL.Le
import HasCASL.As
import HasCASL.AsUtils
import HasCASL.Builtin

import THF.Logic_THF
import THF.Cons as THFCons

-- | The identity of the comorphism
data HasCASL2THF = HasCASL2THF deriving Show

instance Language HasCASL2THF

instance Comorphism HasCASL2THF
                HasCASL Sublogic
                BasicSpec HCAS.Sentence SymbItems SymbMapItems
                Env Morphism Symbol RawSymbol ()
                THF ()
                () THFCons.Sentence () ()
                () THFMorphism THFCons.Symbol () () where
    sourceLogic HasCASL2THF = HasCASL
    sourceSublogic HasCASL2THF = top
    targetLogic HasCASL2THF = THF
