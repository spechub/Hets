{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  portable

Coding out subsorting, lifted tot eh level of CoCASL 
-}

module Comorphisms.CoCASL2CoPCFOL where

import Logic.Logic
import Logic.Comorphism
import qualified Common.Lib.Set as Set

-- CoCASL
import CoCASL.Logic_CoCASL
import CoCASL.AS_CoCASL
import CoCASL.StatAna
import qualified CoCASL.Sublogic
import CASL.AS_Basic_CASL
import CASL.Morphism
import CASL.Sublogic
import CASL.Inject
import CASL.Project
import Comorphisms.CASL2PCFOL

-- | The identity of the comorphism
data CoCASL2CoPCFOL = CoCASL2CoPCFOL deriving (Show)

instance Language CoCASL2CoPCFOL -- default definition is okay

instance Comorphism CoCASL2CoPCFOL
               CoCASL CoCASL.Sublogic.CoCASL_Sublogics
               C_BASIC_SPEC CoCASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CSign 
               CoCASLMor
               CASL.Morphism.Symbol CASL.Morphism.RawSymbol ()
               CoCASL CoCASL.Sublogic.CoCASL_Sublogics
               C_BASIC_SPEC CoCASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CSign 
               CoCASLMor
               CASL.Morphism.Symbol CASL.Morphism.RawSymbol () where
    sourceLogic CoCASL2CoPCFOL = CoCASL
    sourceSublogic CoCASL2CoPCFOL = 
      CoCASL.Sublogic.CoCASL_SL 
          { CoCASL.Sublogic.has_co = True,
            CoCASL.Sublogic.casl = 
             CASL_SL  { has_sub = True, 
                        has_part = True, 
                        has_cons = True,
                        has_eq = True,
                        has_pred = True,
                        which_logic = FOL
                      }
          } 
    targetLogic CoCASL2CoPCFOL = CoCASL
    targetSublogic CoCASL2CoPCFOL = 
      CoCASL.Sublogic.CoCASL_SL 
          { CoCASL.Sublogic.has_co = True,
            CoCASL.Sublogic.casl = 
             CASL_SL  { has_sub = False,  -- subsorting is coded out
                        has_part = True, 
                        has_cons = True,
                        has_eq = True,
                        has_pred = True,
                        which_logic = FOL
                      }
          } 
    map_theory CoCASL2CoPCFOL = mkTheoryMapping ( \ sig -> 
      let e = encodeSig sig in return (e, generateAxioms sig))
      (map_sentence CoCASL2CoPCFOL)
    map_morphism CoCASL2CoPCFOL mor = return 
      (mor  { msource =  encodeSig $ msource mor,
              mtarget =  encodeSig $ mtarget mor })
      -- other components need not to be adapted!
    map_sentence CoCASL2CoPCFOL _ = return . cf2CFormula
    map_symbol CoCASL2CoPCFOL = Set.singleton . id

cf2CFormula :: FORMULA C_FORMULA -> FORMULA C_FORMULA
cf2CFormula = projFormula Partial projC_Formula . injFormula injC_Formula 

projC_Formula, injC_Formula :: C_FORMULA -> C_FORMULA
projC_Formula = foldC_Formula (projRecord Partial projC_Formula) mapCoRecord
injC_Formula = foldC_Formula (injRecord injC_Formula) mapCoRecord
