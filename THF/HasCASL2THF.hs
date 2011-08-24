{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Comorphism from HasCASL to THF
Copyright   :  (c) A. Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Alexis.Tsogias@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from HasCASL to THF.
-}

module Comorphisms.HasCASL2THF where

import Logic.Logic as Logic
import Logic.Comorphism

import Common.ProofTree

import HasCASL.Logic_HasCASL
import HasCASL.Sublogic
import HasCASL.Le
import HasCASL.As
import HasCASL.AsUtils
import HasCASL.Builtin

import THF.Logic_THF
import THF.Cons
import THF.Sign

--------------------------------------------------------------------------------
-- Todo:
--      * move this file from Hets/THF to Hets/Comorphisms
--------------------------------------------------------------------------------

-- | The identity of the comorphism
data HasCASL2THF = HasCASL2THF deriving Show

instance Language HasCASL2THF

instance Comorphism HasCASL2THF
                HasCASL Sublogic
                BasicSpec Sentence SymbItems SymbMapItems
                Env Morphism Symbol RawSymbol ()
                THF ()
                BasicSpecTHF SentenceTHF () ()
                SignTHF MorphismTHF SymbolTHF () ProofTree where
    sourceLogic HasCASL2THF = HasCASL
    sourceSublogic HasCASL2THF = reqSubLogicForTHF0
    targetLogic HasCASL2THF = THF
    mapSublogic HasCASL2THF = error "not implementet yet"
    map_theory HasCASL2THF = error "not implementet yet"
    map_morphism HasCASL2THF = error "not implementet yet"


reqSubLogicForTHF0 :: Sublogic
reqSubLogicForTHF0 = Sublogic
    { has_sub = True
    , has_part = False
    , has_eq = True
    , has_pred = True
    , type_classes = NoClasses
    , has_polymorphism = True
    , has_type_constructors = True
    , which_logic = HOL }
