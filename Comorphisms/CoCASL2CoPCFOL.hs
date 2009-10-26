{- |
Module      :  $Header$
Description :  Extension of CASL2PCFOL to CoCASL
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Coding out subsorting, lifted tot eh level of CoCASL
-}

module Comorphisms.CoCASL2CoPCFOL where

import Logic.Logic
import Logic.Comorphism
import qualified Data.Set as Set
import Common.AS_Annotation

-- CoCASL
import CoCASL.Logic_CoCASL
import CoCASL.AS_CoCASL
import CoCASL.StatAna
import CoCASL.Sublogic
import CASL.Sublogic as SL
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.Inject
import CASL.Project
import CASL.Monoton
import Comorphisms.CASL2PCFOL
import Comorphisms.CASL2CoCASL

-- | The identity of the comorphism
data CoCASL2CoPCFOL = CoCASL2CoPCFOL deriving (Show)

instance Language CoCASL2CoPCFOL -- default definition is okay

instance Comorphism CoCASL2CoPCFOL
               CoCASL CoCASL_Sublogics
               C_BASIC_SPEC CoCASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CSign
               CoCASLMor
               Symbol RawSymbol ()
               CoCASL CoCASL_Sublogics
               C_BASIC_SPEC CoCASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CSign
               CoCASLMor
               Symbol RawSymbol () where
    sourceLogic CoCASL2CoPCFOL = CoCASL
    sourceSublogic CoCASL2CoPCFOL = SL.caslTop
    targetLogic CoCASL2CoPCFOL = CoCASL
    mapSublogic CoCASL2CoPCFOL sl = Just $
          sublogics_max need_horn sl
            { sub_features = NoSub  -- subsorting is coded out
            , has_part = True
            , has_eq = True
            }
    map_theory CoCASL2CoPCFOL = mkTheoryMapping ( \ sig ->
      let e = encodeSig sig in return
      (e, map (mapNamed $ injFormula injC_Formula) (monotonicities sig)
          ++ map (mapNamed mapSen) (generateAxioms sig)))
      (map_sentence CoCASL2CoPCFOL)
    map_morphism CoCASL2CoPCFOL mor = return
      (mor  { msource = encodeSig $ msource mor,
              mtarget = encodeSig $ mtarget mor })
      -- other components need not to be adapted!
    map_sentence CoCASL2CoPCFOL _ = return . cf2CFormula
    map_symbol CoCASL2CoPCFOL _ = Set.singleton . id
    has_model_expansion CoCASL2CoPCFOL = True
    is_weakly_amalgamable CoCASL2CoPCFOL = True

cf2CFormula :: FORMULA C_FORMULA -> FORMULA C_FORMULA
cf2CFormula = projFormula Partial projC_Formula . injFormula injC_Formula

projC_Formula, injC_Formula :: C_FORMULA -> C_FORMULA
projC_Formula = foldC_Formula (projRecord Partial projC_Formula) mapCoRecord
injC_Formula = foldC_Formula (injRecord injC_Formula) mapCoRecord
