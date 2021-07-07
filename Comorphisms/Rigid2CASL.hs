{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/Rigid2CASL.hs
Description :  code out partiality
Copyright   :  (c) M. Codescu, IMAR, 2018
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mscodescu@gmail.com
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

Comorphism from RigidCASL to HPAR that works like

-}

module Comorphisms.Rigid2CASL where

import Logic.Logic
import Logic.Comorphism
import Common.ProofTree
import Common.Result
import Common.AS_Annotation

-- Rigid CASL
import qualified RigidCASL.Logic_RigidCASL as RLogic
import qualified RigidCASL.Sign as RSign
import qualified RigidCASL.AS_Rigid as RBasic
import qualified RigidCASL.Morphism as RMorphism

-- CASL
import qualified CASL.Logic_CASL as CLogic
import qualified CASL.AS_Basic_CASL as CBasic
import qualified CASL.Sign as CSign
import qualified CASL.Morphism as CMor
import CASL.Sublogic

-- base comorphism
import qualified Comorphisms.CASL2SubCFOL as BaseCom
-- | The identity of the comorphism
data Rigid2CASL = Rigid2CASL deriving (Show)

instance Language Rigid2CASL -- default definition is okay

instance Comorphism Rigid2CASL
          RLogic.RigidCASL ()
          RBasic.R_BASIC_SPEC CBasic.CASLFORMULA
                              CBasic.SYMB_ITEMS
                              CBasic.SYMB_MAP_ITEMS
          RSign.RSign
          RMorphism.RigidMor
          RBasic.RigidSymbol CMor.RawSymbol ()
          CLogic.CASL CASL_Sublogics
          CLogic.CASLBasicSpec CBasic.CASLFORMULA
                               CBasic.SYMB_ITEMS
                               CBasic.SYMB_MAP_ITEMS
          CSign.CASLSign
          CMor.CASLMor
          CSign.Symbol CMor.RawSymbol ProofTree where
    sourceLogic Rigid2CASL = RLogic.RigidCASL
    sourceSublogic Rigid2CASL = ()
    targetLogic Rigid2CASL = CLogic.CASL
    mapSublogic Rigid2CASL _ =
      Just cFol { cons_features = emptyMapConsFeature }
    map_theory Rigid2CASL = mapTheory
    map_morphism Rigid2CASL = undefined
    map_sentence Rigid2CASL sig sen =
      map_sentence (BaseCom.CASL2SubCFOL True BaseCom.NoMembershipOrCast)
                   (RSign.caslSign sig) sen
    map_symbol Rigid2CASL _ = undefined
    has_model_expansion Rigid2CASL = True
    com_path Rigid2CASL = "Comorphisms.Rigid2CASL"

mapTheory :: (RSign.RSign, [Named CBasic.CASLFORMULA]) ->
             Result (CSign.CASLSign, [Named CBasic.CASLFORMULA])
mapTheory (sig, nsens) = do
 let csig = RSign.caslSign sig
 (csig', csens') <-
   map_theory (BaseCom.CASL2SubCFOL True BaseCom.NoMembershipOrCast)
              (csig, nsens)
 return (csig', csens')
