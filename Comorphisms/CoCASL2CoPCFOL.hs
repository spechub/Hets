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
import Common.Id
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.AS_Annotation
import Data.List

-- CoCASL
import CoCASL.Logic_CoCASL
import CoCASL.CoCASLSign
import CoCASL.AS_CoCASL
import CoCASL.StatAna
import qualified CoCASL.Sublogic
import CASL.AS_Basic_CASL
import CASL.Morphism
import CASL.Sublogic
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
    map_sentence CoCASL2CoPCFOL _ = return . f2Formula
    map_symbol CoCASL2CoPCFOL = Set.singleton . id

