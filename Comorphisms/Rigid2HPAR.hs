{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/Rigid2HPAR.hs
Description :  embedding from RigidCASL to HPAR
Copyright   :  (c) M. Codescu, IMAR, 2018
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mscodescu@gmail.com
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from RigidCASL to HPAR.

-}

module Comorphisms.Rigid2HPAR where

import Logic.Logic
import Logic.Comorphism
import qualified Data.Set as Set
import qualified Data.Map as Map
--import Common.ProofTree
import Common.Result
import Common.AS_Annotation
import Common.Id

-- Rigid CASL
import qualified RigidCASL.Logic_RigidCASL as RLogic 
import qualified RigidCASL.Sign as RSign
import qualified RigidCASL.AS_Rigid as RBasic
import qualified RigidCASL.Morphism as RMorphism

-- HPAR
import qualified HPAR.Logic_HPAR as HLogic
import qualified HPAR.AS_Basic_HPAR as HBasic
import qualified HPAR.Sign as HSign
import qualified HPAR.Morphism as HMorphism
import qualified HPAR.Symbol as HSym

-- CASL
import qualified CASL.AS_Basic_CASL as CBasic
import qualified CASL.Sign as CSign
import qualified CASL.Morphism as CMor

-- | The identity of the comorphism
data Rigid2HPAR = Rigid2HPAR deriving (Show)

instance Language Rigid2HPAR -- default definition is okay

instance Comorphism Rigid2HPAR
               RLogic.RigidCASL ()
               RBasic.R_BASIC_SPEC CBasic.CASLFORMULA CBasic.SYMB_ITEMS CBasic.SYMB_MAP_ITEMS
               RSign.RSign
               RMorphism.RigidMor
               CSign.Symbol CMor.RawSymbol ()
               HLogic.HPAR ()
               HBasic.H_BASIC_SPEC HBasic.HFORMULA HBasic.H_SYMB_ITEMS 
               CBasic.SYMB_MAP_ITEMS
               HSign.HSign HMorphism.HMorphism HSym.HSymbol CMor.RawSymbol () where
    sourceLogic Rigid2HPAR = RLogic.RigidCASL
    sourceSublogic Rigid2HPAR = ()
    targetLogic Rigid2HPAR = HLogic.HPAR
    mapSublogic Rigid2HPAR _ = Just ()
    map_theory Rigid2HPAR = mapTheory
    map_morphism Rigid2HPAR = undefined
    map_sentence Rigid2HPAR =  undefined
    map_symbol Rigid2HPAR _ = undefined
    has_model_expansion Rigid2HPAR = True
    is_weakly_amalgamable Rigid2HPAR = True
    isInclusionComorphism Rigid2HPAR = True

mapTheory :: (RSign.RSign, [Named CBasic.CASLFORMULA]) ->
             Result (HSign.HSign, [Named HBasic.HFORMULA])
mapTheory (sig, nsens) = do
 let tsig = HSign.HSign {HSign.baseSig = sig,
                         HSign.noms = Set.singleton $ genName "i",
                         HSign.mods = Map.empty}
     tsens = map mapNamedSen nsens
 return (tsig, tsens)

mapNamedSen :: Named CBasic.CASLFORMULA -> Named HBasic.HFORMULA
mapNamedSen nsen = let
 sen = sentence nsen
 trans = HBasic.AtState (genToken "i") (HBasic.Base_formula sen nullRange) nullRange
                    in
 nsen {sentence = trans}


