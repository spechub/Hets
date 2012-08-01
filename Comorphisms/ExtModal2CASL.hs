{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Copyright   :  (c) Mihaela Turcu, DFKI 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  m.turcu@jacobs-university.de
Stability   :  
Portability :  
-}

module Comorphisms.ExtModal2CASL where

import Logic.Logic
import Logic.Comorphism
import Common.ProofTree
import Common.Id
import qualified Common.Lib.Rel as Rel

-- CASL
import CASL.Logic_CASL
import CASL.Sublogic as SL
import CASL.Sign
import CASL.AS_Basic_CASL
import CASL.Morphism

-- ExtModalCASL
import ExtModal.Logic_ExtModal
import ExtModal.AS_ExtModal
--import ExtModal.ExtModalSign
import ExtModal.Sublogic

data ExtModal2CASL = ExtModal2CASL deriving (Show)
instance Language ExtModal2CASL

instance Comorphism ExtModal2CASL
               ExtModal Sublogic EM_BASIC_SPEC ExtModalFORMULA SYMB_ITEMS 
               SYMB_MAP_ITEMS ExtModalSign ExtModalMorph
               Symbol RawSymbol ()
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol ProofTree where
    sourceLogic ExtModal2CASL = ExtModal
    sourceSublogic ExtModal2CASL = maxSublogic
    targetLogic ExtModal2CASL = CASL
    mapSublogic ExtModal2CASL _ = Just SL.caslTop
    map_theory ExtModal2CASL (sig, _sens) = case transSig sig of
      mme -> return (mme, [])
    {-
    map_morphism ExtModal2CASL = return . mapMor
    map_sentence ExtModal2CASL sig = return . transSen sig
    map_symbol ExtModal2CASL _ = Set.singleton . mapSym
    -}
    has_model_expansion ExtModal2CASL = True
    is_weakly_amalgamable ExtModal2CASL = True


transSig :: ExtModalSign -> CASLSign
transSig sign = let 
   s1 = embedSign () sign 
   _modExt = extendedInfo sign
   fws = mkId [mkSimpleId "g_World"]
   s2 = s1 {sortRel = Rel.insertKey fws $ sortRel s1}
   in s2



{-

       flexOps' = MapSet.fromMap . Map.foldWithKey (addWorld_OP fws)
                                    Map.empty $ MapSet.toMap flexibleOps
       flexPreds' = MapSet.fromMap . addWorldRels True relsTermMod
                    . addWorldRels False relsMod
                    . Map.foldWithKey (addWorld_PRED fws)
                                    Map.empty $ MapSet.toMap
-}

