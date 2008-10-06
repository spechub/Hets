{- |
Module      :  $Header$
Description :  Extension of CASL2SubCFOL to CoCASL
Copyright   :  (c) Till Mossakowski, C.Maeder, Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Comorphism)

coding out partiality, lifted to the level of CoCASL
-}

module Comorphisms.CoCASL2CoSubCFOL where

import Logic.Logic
import Logic.Comorphism

-- CoCASL
import CoCASL.Logic_CoCASL
import CoCASL.AS_CoCASL
import CoCASL.StatAna
import CoCASL.Sublogic
import CASL.Sublogic as SL
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.Sublogic
import CASL.Fold
import CASL.Simplify
import Comorphisms.CASL2SubCFOL
import Comorphisms.CASL2CoCASL

import qualified Data.Map as Map
import qualified Data.Set as Set
import Common.AS_Annotation
import Common.ProofUtils

-- | The identity of the comorphism
data CoCASL2CoSubCFOL = CoCASL2CoSubCFOL deriving (Show)

instance Language CoCASL2CoSubCFOL -- default definition is okay

instance Comorphism CoCASL2CoSubCFOL
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
    sourceLogic CoCASL2CoSubCFOL = CoCASL
    sourceSublogic CoCASL2CoSubCFOL = SL.caslTop
    targetLogic CoCASL2CoSubCFOL = CoCASL
    mapSublogic CoCASL2CoSubCFOL sl = Just $
       if has_part sl then sl
        { has_part    = False -- partiality is coded out
        , has_pred    = True
        , which_logic = max Horn $ which_logic sl
        , has_eq      = True} else sl
    map_theory CoCASL2CoSubCFOL (sig, sens) =
        let bsrts = sortsWithBottom (formulaTreatment defaultCASL2SubCFOL)
              sig $ Set.unions $ map (botCoFormulaSorts . sentence) sens
            e = encodeSig bsrts sig
            sens1 = map (mapNamed mapSen) $ generateAxioms
                    (uniqueBottom defaultCASL2SubCFOL) bsrts sig
            sens2 = map (mapNamed (simplifyFormula simC_FORMULA
                                   . codeCoFormula bsrts)) sens
        in return (e, nameAndDisambiguate $ sens1 ++ sens2)
    map_morphism CoCASL2CoSubCFOL mor@Morphism{msource = src, mtarget = tar} =
        let mkBSrts s = sortsWithBottom
              (formulaTreatment defaultCASL2SubCFOL) s Set.empty
        in return mor
            { msource = encodeSig (mkBSrts src) src
            , mtarget = encodeSig (mkBSrts tar) tar
            , fun_map = Map.map (\ (i, _) -> (i, Total)) $ fun_map mor }
    map_sentence CoCASL2CoSubCFOL sig  sen =
        return $ simplifyFormula simC_FORMULA $ codeCoFormula
           (sortsWithBottom (formulaTreatment defaultCASL2SubCFOL)
            sig $ botCoFormulaSorts sen) sen
    map_symbol CoCASL2CoSubCFOL s =
        Set.singleton s {symbType = totalizeSymbType $ symbType s}
    has_model_expansion CoCASL2CoSubCFOL = True
    is_weakly_amalgamable CoCASL2CoSubCFOL = True

codeCoRecord :: Set.Set SORT
             -> Record C_FORMULA (FORMULA C_FORMULA) (TERM C_FORMULA)
codeCoRecord bsrts =
    codeRecord (uniqueBottom defaultCASL2SubCFOL) bsrts $ codeC_FORMULA bsrts

codeCoFormula :: Set.Set SORT -> FORMULA C_FORMULA -> FORMULA C_FORMULA
codeCoFormula = foldFormula . codeCoRecord

codeC_FORMULA :: Set.Set SORT -> C_FORMULA -> C_FORMULA
codeC_FORMULA bsrts = foldC_Formula (codeCoRecord bsrts) mapCoRecord
  {foldCoSort_gen_ax = \ _ s o b -> CoSort_gen_ax s (map totalizeOpSymb o) b}

simC_FORMULA :: C_FORMULA -> C_FORMULA
simC_FORMULA = foldC_Formula (simplifyRecord simC_FORMULA) mapCoRecord

botCoSorts :: C_FORMULA -> Set.Set SORT
botCoSorts =
    foldC_Formula (botSorts botCoSorts) (constCoRecord Set.unions Set.empty)

botCoFormulaSorts :: FORMULA C_FORMULA -> Set.Set SORT
botCoFormulaSorts = foldFormula $ botSorts botCoSorts
