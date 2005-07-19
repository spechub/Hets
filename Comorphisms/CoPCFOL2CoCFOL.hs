{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  portable

Coding out subsorting, lifted to the level of CoCASL 
-}

module Comorphisms.CoPCFOL2CoCFOL where

import Logic.Logic
import Logic.Comorphism
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set

-- CoCASL
import CoCASL.Logic_CoCASL
import CoCASL.CoCASLSign
import CoCASL.AS_CoCASL
import CoCASL.StatAna
import qualified CoCASL.Sublogic
import CASL.AS_Basic_CASL
import CASL.Morphism
import CASL.Sublogic
import CASL.Simplify
import Comorphisms.PCFOL2CFOL

-- | The identity of the comorphism
data CoPCFOL2CoCFOL = CoPCFOL2CoCFOL deriving (Show)

instance Language CoPCFOL2CoCFOL -- default definition is okay

instance Comorphism CoPCFOL2CoCFOL
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
    sourceLogic CoPCFOL2CoCFOL = CoCASL
    sourceSublogic CoPCFOL2CoCFOL = 
      CoCASL.Sublogic.CoCASL_SL 
          { CoCASL.Sublogic.has_co = True,
            CoCASL.Sublogic.casl = 
             CASL_SL  { has_sub = False, 
                        has_part = True, 
                        has_cons = True,
                        has_eq = True,
                        has_pred = True,
                        which_logic = FOL
                      }
          } 
    targetLogic CoPCFOL2CoCFOL = CoCASL
    targetSublogic CoPCFOL2CoCFOL = 
      CoCASL.Sublogic.CoCASL_SL 
          { CoCASL.Sublogic.has_co = True,
            CoCASL.Sublogic.casl = 
             CASL_SL  { has_sub = False, 
                        has_part = False, -- partiality is coded out 
                        has_cons = True,
                        has_eq = True,
                        has_pred = True,
                        which_logic = FOL
                      }
          } 
    map_theory CoPCFOL2CoCFOL = mkTheoryMapping ( \ sig ->
          let e = sig2FOL sig in return (e, generateFOLAxioms sig)) 
          (map_sentence CoPCFOL2CoCFOL)
    map_morphism CoPCFOL2CoCFOL m = return m
                { msource = sig2FOL $ msource m
                , mtarget = sig2FOL $ mtarget m
                , fun_map = Map.map (\ (i, _) -> (i, Total)) $ 
                            fun_map m }
    map_sentence CoPCFOL2CoCFOL sig = 
        return . simplifyFormula id . totalizeFormula (sortsWithBottom sig) id
    map_symbol CoPCFOL2CoCFOL s = 
      Set.singleton s { symbType = totalizeSymbType $ symbType s }

