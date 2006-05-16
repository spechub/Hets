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
import Common.AS_Annotation

-- CoCASL
import CoCASL.Logic_CoCASL
import CoCASL.AS_CoCASL
import CoCASL.StatAna
import qualified CoCASL.Sublogic as SL
import CASL.AS_Basic_CASL
import CASL.Morphism
import CASL.Sublogic
import CASL.Simplify
import Comorphisms.PCFOL2CFOL
import Comorphisms.CASL2CoCASL

-- | The identity of the comorphism
data CoPCFOL2CoCFOL = CoPCFOL2CoCFOL deriving (Show)

instance Language CoPCFOL2CoCFOL -- default definition is okay

instance Comorphism CoPCFOL2CoCFOL
               CoCASL SL.CoCASL_Sublogics
               C_BASIC_SPEC CoCASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CSign
               CoCASLMor
               CASL.Morphism.Symbol CASL.Morphism.RawSymbol ()
               CoCASL SL.CoCASL_Sublogics
               C_BASIC_SPEC CoCASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CSign
               CoCASLMor
               CASL.Morphism.Symbol CASL.Morphism.RawSymbol () where
    sourceLogic CoPCFOL2CoCFOL = CoCASL
    sourceSublogic CoPCFOL2CoCFOL =
      SL.top { SL.casl = (SL.casl SL.top) { sub_features = NoSub } }
    targetLogic CoPCFOL2CoCFOL = CoCASL
    mapSublogic CoPCFOL2CoCFOL sl = sl
          { SL.casl = (SL.casl sl)
               { has_part = False -- partiality is coded out
               , has_eq = True
               , has_pred = True
               }
          }
    map_theory CoPCFOL2CoCFOL = mkTheoryMapping ( \ sig ->
          let e = sig2FOL sig in return (e, map (mapNamed mapSen)
                                              $ generateFOLAxioms sig))
          (map_sentence CoPCFOL2CoCFOL)
    map_morphism CoPCFOL2CoCFOL m = return m
                { msource = sig2FOL $ msource m
                , mtarget = sig2FOL $ mtarget m
                , fun_map = Map.map (\ (i, _) -> (i, Total)) $
                            fun_map m }
    map_sentence CoPCFOL2CoCFOL sig = let bsrts = sortsWithBottom sig in
        return . simplifyFormula simC_FORMULA .
               totalizeFormula bsrts (totC_FORMULA bsrts)
    map_symbol CoPCFOL2CoCFOL s =
      Set.singleton s { symbType = totalizeSymbType $ symbType s }

simC_FORMULA :: C_FORMULA -> C_FORMULA
simC_FORMULA = foldC_Formula (simplifyRecord simC_FORMULA) mapCoRecord

totC_FORMULA :: Set.Set SORT -> C_FORMULA -> C_FORMULA
totC_FORMULA bsrts = foldC_Formula (totalRecord bsrts $ totC_FORMULA bsrts)
    mapCoRecord { foldCoSort_gen_ax = \ _ s o b ->
                  CoSort_gen_ax s (map totalizeOpSymb o) b }
