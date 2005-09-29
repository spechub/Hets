{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski and Uni Bremen 2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from CASL to ColCASL.

-}

module Comorphisms.CASL2CoCASL where

import Logic.Logic
import Logic.Comorphism
import qualified Common.Lib.Set as Set

-- CASL
import CASL.Logic_CASL 
import CASL.Sublogic
import CASL.Sign
import CASL.AS_Basic_CASL
import CASL.Morphism
import CASL.Fold

-- CoCASLCASL
import CoCASL.Logic_CoCASL
import CoCASL.AS_CoCASL
import CoCASL.CoCASLSign
import CoCASL.StatAna (CSign)
import qualified CoCASL.Sublogic

-- | The identity of the comorphism
data CASL2CoCASL = CASL2CoCASL deriving (Show)

instance Language CASL2CoCASL -- default definition is okay

instance Comorphism CASL2CoCASL
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign 
               CASLMor
               Symbol RawSymbol ()
               CoCASL CoCASL.Sublogic.CoCASL_Sublogics
               C_BASIC_SPEC CoCASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CSign 
               CoCASLMor
               Symbol RawSymbol () where
    sourceLogic CASL2CoCASL = CASL
    sourceSublogic CASL2CoCASL = CASL_SL
                      { sub_features = Sub, 
                        has_part = True,
                        cons_features = SortGen { emptyMapping = False,
                                                  onlyInjConstrs = False},
                        has_eq = True,
                        has_pred = True,
                        which_logic = FOL
                      }
    targetLogic CASL2CoCASL = CoCASL
    targetSublogic CASL2CoCASL = 
        CoCASL.Sublogic.CoCASL_SL 
          { CoCASL.Sublogic.has_co = False, 
            CoCASL.Sublogic.casl = CASL.Sublogic.top }
    map_theory CASL2CoCASL = return . simpleTheoryMapping mapSig mapSen
    map_morphism CASL2CoCASL = return . mapMor
    map_sentence CASL2CoCASL _ = return . mapSen
    map_symbol CASL2CoCASL = Set.singleton . mapSym

mapSig :: CASLSign -> CSign
mapSig sign = 
     (emptySign emptyCoCASLSign) {sortSet = sortSet sign
               , sortRel = sortRel sign
               , opMap = opMap sign
               , assocOps = assocOps sign
               , predMap = predMap sign }

mapMor :: CASLMor -> CoCASLMor
mapMor m = Morphism {msource = mapSig $ msource m
                   , mtarget = mapSig $ mtarget m
                   , sort_map = sort_map m
                   , fun_map = fun_map m
                   , pred_map = pred_map m
                   , extended_map = ()}


mapSym :: Symbol -> Symbol
mapSym = id  -- needs to be changed once CoCASL symbols are added

mapSen :: CASLFORMULA -> CoCASLFORMULA
mapSen = foldFormula $ mapRecord (const $ error "CASL2CoCASL.mapSen")
