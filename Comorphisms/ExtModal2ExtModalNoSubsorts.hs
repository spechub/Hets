{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, DeriveGeneric #-}
{- |
Module      :  ./Comorphisms/ExtModal2ExtModalNoSubsorts.hs
Description :  coding out subsorting
Copyright   :  (c) C. Maeder DFKI GmbH 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

Coding out subsorting (SubPCFOL= -> PCFOL=),
   following Chap. III:3.1 of the CASL Reference Manual
-}

module Comorphisms.ExtModal2ExtModalNoSubsorts where

import Logic.Logic
import Logic.Comorphism

import qualified Data.HashSet as Set

import Common.AS_Annotation

-- CASL
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.Inject
import CASL.Project
import CASL.Monoton
import CASL.Sublogic

import ExtModal.Logic_ExtModal
import ExtModal.AS_ExtModal
import ExtModal.StatAna
import ExtModal.Sublogic as EM

import Comorphisms.CASL2PCFOL

import GHC.Generics (Generic)
import Data.Hashable

-- | The identity of the comorphism
data ExtModal2ExtModalNoSubsorts = ExtModal2ExtModalNoSubsorts 
 deriving (Show, Generic)

instance Hashable ExtModal2ExtModalNoSubsorts

instance Language ExtModal2ExtModalNoSubsorts -- default definition is okay

instance Comorphism ExtModal2ExtModalNoSubsorts
               ExtModal ExtModalSL EM_BASIC_SPEC ExtModalFORMULA SYMB_ITEMS
               SYMB_MAP_ITEMS ExtModalSign ExtModalMorph
               Symbol RawSymbol ()
               ExtModal ExtModalSL EM_BASIC_SPEC ExtModalFORMULA SYMB_ITEMS
               SYMB_MAP_ITEMS ExtModalSign ExtModalMorph
               Symbol RawSymbol () where
    sourceLogic ExtModal2ExtModalNoSubsorts = ExtModal
    sourceSublogic ExtModal2ExtModalNoSubsorts = mkTop maxSublogic
    targetLogic ExtModal2ExtModalNoSubsorts = ExtModal
    mapSublogic ExtModal2ExtModalNoSubsorts sl = Just
      $ if has_sub sl then -- subsorting is coded out
            sl { sub_features = NoSub
               , has_part = True
               , which_logic = max Horn $ which_logic sl
               , has_eq = True}
        else sl
    map_theory ExtModal2ExtModalNoSubsorts = mkTheoryMapping (\ sig ->
      let e = encodeSig sig in
      return (e, map (mapNamed injEMFormula) (monotonicities sig)
                 ++ generateAxioms sig))
      (map_sentence ExtModal2ExtModalNoSubsorts)
    map_morphism ExtModal2ExtModalNoSubsorts mor = return
      (mor { msource = encodeSig $ msource mor,
              mtarget = encodeSig $ mtarget mor })
    map_sentence ExtModal2ExtModalNoSubsorts _ =
      return . projEMFormula . injEMFormula
    map_symbol ExtModal2ExtModalNoSubsorts _ = Set.singleton . id
    has_model_expansion ExtModal2ExtModalNoSubsorts = True
    is_weakly_amalgamable ExtModal2ExtModalNoSubsorts = True

projEMFormula :: FORMULA EM_FORMULA -> FORMULA EM_FORMULA
projEMFormula = projFormula Partial projEM

projEM :: EM_FORMULA -> EM_FORMULA
projEM = mapExtForm projEMFormula

injEMFormula :: FORMULA EM_FORMULA -> FORMULA EM_FORMULA
injEMFormula = injFormula injEM

injEM :: EM_FORMULA -> EM_FORMULA
injEM = mapExtForm injEMFormula
