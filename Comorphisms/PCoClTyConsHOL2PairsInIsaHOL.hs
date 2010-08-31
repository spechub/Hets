{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  normalising translation of a HasCASL subset to Isabelle
Copyright   :  (c) C. Maeder, DFKI 2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

An embedding comorphism from HasCASL without subtypes to
Isabelle-HOL.
-}

module Comorphisms.PCoClTyConsHOL2PairsInIsaHOL
    (PCoClTyConsHOL2PairsInIsaHOL(..)) where

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
data PCoClTyConsHOL2PairsInIsaHOL = PCoClTyConsHOL2PairsInIsaHOL deriving Show

instance Language PCoClTyConsHOL2PairsInIsaHOL where
  language_name PCoClTyConsHOL2PairsInIsaHOL = "NormalisingTranslation"

instance Comorphism PCoClTyConsHOL2PairsInIsaHOL
               HasCASL Sublogic
               BasicSpec Le.Sentence SymbItems SymbMapItems
               Env Morphism
               Symbol RawSymbol ()
               Isabelle () () Isa.Sentence () ()
               Isa.Sign
               IsabelleMorphism () () ()  where
    sourceLogic PCoClTyConsHOL2PairsInIsaHOL = HasCASL
    sourceSublogic PCoClTyConsHOL2PairsInIsaHOL = noSubtypes
    targetLogic PCoClTyConsHOL2PairsInIsaHOL = Isabelle
    mapSublogic cid sl = if sl `isSubElem` sourceSublogic cid
                       then Just () else Nothing
    map_theory PCoClTyConsHOL2PairsInIsaHOL th = do
      (sig, sens) <- mapTheory New simpForOption th
      return (sig { baseSig = MainHC_thy }, sens)
    map_morphism = mapDefaultMorphism
    map_sentence PCoClTyConsHOL2PairsInIsaHOL sign phi =
       transSentence sign (typeToks sign) New simpForOption phi
    isInclusionComorphism PCoClTyConsHOL2PairsInIsaHOL = True
    has_model_expansion PCoClTyConsHOL2PairsInIsaHOL = True
