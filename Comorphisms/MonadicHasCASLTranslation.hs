{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  translating a HasCASL subset to Isabelle
Copyright   :  (c) C. Maeder, DFKI 2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from HasCASL without subtypes to
Isabelle-HOL.  Partial functions yield an option or bool result in
Isabelle. Case-terms and constructor classes are not supported yet.
-}

module Comorphisms.MonadicHasCASLTranslation
    (MonadicHasCASL2IsabelleHOL(..)) where

import Comorphisms.PPolyTyConsHOL2IsaUtils
import Logic.Logic as Logic
import Logic.Comorphism

import HasCASL.Logic_HasCASL
import HasCASL.Sublogic
import HasCASL.As
import HasCASL.Le as Le

import Isabelle.IsaSign as Isa
import Isabelle.Logic_Isabelle

-- | The identity of the comorphism
data MonadicHasCASL2IsabelleHOL = MonadicHasCASL2IsabelleHOL deriving Show

instance Language MonadicHasCASL2IsabelleHOL where
  language_name MonadicHasCASL2IsabelleHOL = "MonadicTranslation"

instance Comorphism MonadicHasCASL2IsabelleHOL
               HasCASL Sublogic
               BasicSpec Le.Sentence SymbItems SymbMapItems
               Env Morphism
               Symbol RawSymbol ()
               Isabelle () () Isa.Sentence () ()
               Isa.Sign
               IsabelleMorphism () () ()  where
    sourceLogic MonadicHasCASL2IsabelleHOL = HasCASL
    sourceSublogic MonadicHasCASL2IsabelleHOL = noSubtypes
    targetLogic MonadicHasCASL2IsabelleHOL = Isabelle
    mapSublogic cid sl = if sl `isSubElem` sourceSublogic cid
                       then Just () else Nothing
    map_theory MonadicHasCASL2IsabelleHOL =
        mapTheory (Old NoSimpLift) simpForOption
    map_morphism = mapDefaultMorphism
    map_sentence MonadicHasCASL2IsabelleHOL sign phi =
        transSentence sign (typeToks sign) (Old NoSimpLift) simpForOption phi
    isInclusionComorphism MonadicHasCASL2IsabelleHOL = True
    has_model_expansion MonadicHasCASL2IsabelleHOL = True
