{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski and Uni Bremen 2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  M.Roggenbach@swansea.ac.uk
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from CASL to CspCASL.

-}

module Comorphisms.CASL2CspCASL where

import Logic.Logic
import Logic.Comorphism
import Common.Id
import Common.Lib.State
import Common.AS_Annotation
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set

-- CASL
import CASL.Logic_CASL 
import CASL.Sublogic
import CASL.Sign
import CASL.AS_Basic_CASL
import CASL.Morphism

-- CspCASL
import CspCASL.Logic_CspCASL
import CspCASL.AS_CSP_CASL
import CspCASL.SignCSP


-- | The identity of the comorphism
data CASL2CspCASL = CASL2CspCASL deriving (Show)

instance Language CASL2CspCASL -- default definition is okay

instance Comorphism CASL2CspCASL
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign 
               CASLMor
               Symbol RawSymbol ()
               CspCASL ()
               Basic_CSP_CASL_C_SPEC () SYMB_ITEMS SYMB_MAP_ITEMS
               CSPSign
               CSPMorphism
               () () () where
    sourceLogic CASL2CspCASL = CASL
    sourceSublogic CASL2CspCASL = CASL_SL
                      { sub_features = Sub, -- simple subsorting in CspCASL
                        has_part = True,
                        cons_features = SortGen { emptyMapping = False,
                                                  onlyInjConstrs = False},
                        has_eq = True,
                        has_pred = True,
                        which_logic = FOL
                      }
    targetLogic CASL2CspCASL = CspCASL
    targetSublogic CASL2CspCASL = ()
    map_theory CASL2CspCASL = return . simpleTheoryMapping mapSig (const ())
    map_morphism CASL2CspCASL = return . mapMor
    map_sentence CASL2CspCASL sig = return . (const ()) -- toSentence sig
    --map_symbol CASL2CspCASL = Set.singleton . mapSym

mapSig :: CASLSign -> CSPSign
mapSig sign = 
     (emptySign emptyCSPAddSign) {sortSet = sortSet sign
               , sortRel = sortRel sign
               , opMap = opMap sign
               , assocOps = assocOps sign
               , predMap = predMap sign }

mapMor :: CASLMor -> CSPMorphism
mapMor m = Morphism {msource = mapSig $ msource m
                   , mtarget = mapSig $ mtarget m
                   , sort_map = sort_map m
                   , fun_map = fun_map m
                   , pred_map = pred_map m
                   , extended_map = 
                       CSPAddMorphism { channelMap = Map.empty,
                                        processMap = Map.empty
                    }}

