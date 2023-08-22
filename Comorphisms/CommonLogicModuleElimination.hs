{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  ./Comorphisms/CommonLogicModuleElimination.hs
Description :  Comorphism from CommonLogic to CommonLogic
Copyright   :  (c) Eugen Kuksa, Uni Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  eugenk@informatik.uni-bremen.de
Stability   :  experimental (not complete: typleclass-instances missing)
Portability :  non-portable (via Logic.Logic)

Translating comorphism from CommonLogic to CommonLogic in order to eliminate
modules.

-}


module Comorphisms.CommonLogicModuleElimination (
        CommonLogicModuleElimination (..)
    )
    where

import Logic.Logic as Logic
import Logic.Comorphism

import Common.ProofTree
import Common.Result
import qualified Common.AS_Annotation as AS_Anno

-- Common Logic
import CommonLogic.AS_CommonLogic
import qualified CommonLogic.Logic_CommonLogic as Logic
import qualified CommonLogic.Sign as Sign
import qualified CommonLogic.Symbol as Symbol
import qualified CommonLogic.Morphism as Mor
import qualified CommonLogic.Sublogic as Sl
import CommonLogic.ModuleElimination

data CommonLogicModuleElimination = CommonLogicModuleElimination deriving Show

instance Language CommonLogicModuleElimination where
  language_name CommonLogicModuleElimination = "CommonLogicModuleElimination"

instance Comorphism
    CommonLogicModuleElimination -- comorphism
    Logic.CommonLogic       -- lid domain
    Sl.CommonLogicSL        -- sublogics codomain
    BASIC_SPEC              -- Basic spec domain
    TEXT_META               -- sentence domain
    SYMB_ITEMS              -- symb_items
    SYMB_MAP_ITEMS          -- symbol map items domain
    Sign.Sign               -- signature domain
    Mor.Morphism            -- morphism domain
    Symbol.Symbol           -- symbol domain
    Symbol.Symbol           -- rawsymbol domain
    ProofTree               -- proof tree codomain
    Logic.CommonLogic       -- lid domain
    Sl.CommonLogicSL        -- sublogics codomain
    BASIC_SPEC              -- Basic spec domain
    TEXT_META               -- sentence domain
    SYMB_ITEMS              -- symb_items
    SYMB_MAP_ITEMS          -- symbol map items domain
    Sign.Sign               -- signature domain
    Mor.Morphism            -- morphism domain
    Symbol.Symbol           -- symbol domain
    Symbol.Symbol           -- rawsymbol domain
    ProofTree               -- proof tree codomain
    where
      sourceLogic CommonLogicModuleElimination = Logic.CommonLogic
      sourceSublogic CommonLogicModuleElimination = Sl.top
      targetLogic CommonLogicModuleElimination = Logic.CommonLogic
      mapSublogic CommonLogicModuleElimination = Just . mapSub
      map_theory CommonLogicModuleElimination = mapTheory
      map_morphism CommonLogicModuleElimination = mapMor
      map_sentence CommonLogicModuleElimination = mapSentence
      -- hasCommonLogicModuleElimination_model_expansion  = True -- TODO: check if it is really True


mapSub :: Sl.CommonLogicSL -> Sl.CommonLogicSL
mapSub = id

mapMor :: Mor.Morphism -> Result Mor.Morphism
mapMor = return

mapSentence :: Sign.Sign -> TEXT_META -> Result TEXT_META
mapSentence _ txt = return $ eliminateModules txt

{- -----------------------------------------------------------------------------
MODULE ELIMINATION                                                        --
----------------------------------------------------------------------------- -}


mapTheory :: (Sign.Sign, [AS_Anno.Named TEXT_META])
             -> Result (Sign.Sign, [AS_Anno.Named TEXT_META])
mapTheory (srcSign, srcTexts) =
  return (srcSign,
          map (uncurry AS_Anno.makeNamed . elimModSnd . senAndName) srcTexts)
  where senAndName :: AS_Anno.Named TEXT_META -> (String, TEXT_META)
        senAndName t = (AS_Anno.senAttr t, AS_Anno.sentence t)
        elimModSnd :: (String, TEXT_META) -> (String, TEXT_META)
        elimModSnd (s, t) = (s, eliminateModules t)
