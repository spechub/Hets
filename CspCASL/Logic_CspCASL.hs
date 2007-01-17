{- |
Module      :  $Header$
Copyright   :  (c)  Markus Roggenbach, Till Mossakowski and Uni Bremen 2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  M.Roggenbach@swansea.ac.uk
Stability   :  experimental
Portability :  non-portable(import Logic.Logic)

Here is the place where the class Logic is instantiated for CspCASL.
   Also the instances for Syntax an Category.
-}
{-
   todo:
     - writing real functions
     - Modul Sign.hs mit CSP-CASL-Signaturen und Morphismen, basiernd auf CASL.Sign
          CSP-CASL-Signatur = (CASL-Sig,Menge von Kanalnamen)
          CSP-CASL-Morphismus = (CASL-Morphismus, Kanalnamenabbildung)
                      oder nur CASL-Morphismus
          SYMB_ITEMS SYMB_MAP_ITEMS: erstmal von CASL (d.h. nur CASL-Morphismus)
     - instance Sentences
        Sätze = entweder CASL-Sätze oder CSP-CASL-Sätze
        Rest soweit wie möglich von CASL übernehmen
     - statische Analyse (gemäß Typ in Logic.Logic) schreiben
       und unten für basic_analysis einhängen

    Kür:
     - Teillogiken (instance SemiLatticeWithTop ...)

-}

module CspCASL.Logic_CspCASL(CspCASL(CspCASL)) where

import CspCASL.CspCASL_Keywords (csp_casl_keywords)

import CspCASL.AS_CspCASL
import CspCASL.ATC_CspCASL()
import CspCASL.SignCSP
import CspCASL.StatAnaCSP --(basicAnalysisCspCASL, Basic_CSP_CASL_C_SPEC)
import CspCASL.AS_CSP_CASL

import CASL.AS_Basic_CASL
import CASL.SymbolParser
import CASL.Logic_CASL(CASL(CASL))
import CASL.Sign
import CASL.Morphism

import Logic.Logic
import Common.Lib.Map as Map

-- a dummy datatype for the LogicGraph and for identifying the right
-- instances
data CspCASL = CspCASL deriving (Show)
instance Language CspCASL  -- default definition is okay

instance Category CspCASL CSPSign CSPMorphism
    where
         -- ide :: id -> object -> morphism
         ide CspCASL sigma = 
           let idAdd =
                CSPAddMorphism { channelMap = Map.empty -- ??? too simplistic!
                               , processMap = Map.empty -- ??? too simplistic!
                               }
            in idMor (\ _ _ -> idAdd) sigma
         -- o :: id -> morphism -> morphism -> Maybe morphism
         comp CspCASL = compose (const id) -- ??? too simplistic!
         -- dom, cod :: id -> morphism -> object
         dom CspCASL = msource
         cod CspCASL = mtarget
         -- legal_obj :: id -> object -> Bool
         legal_obj CspCASL _ = fun_err "legall_obj"
         -- legal_mor :: id -> morphism -> Bool
         legal_mor CspCASL _ = fun_err "legal_mor"

-- abstract syntax, parsing (and printing)

instance Syntax CspCASL Basic_CSP_CASL_C_SPEC
                SYMB_ITEMS SYMB_MAP_ITEMS
      where 
         parse_basic_spec CspCASL = Just basicCspCaslCSpec
         parse_symb_items CspCASL = Just $ symbItems csp_casl_keywords
         parse_symb_map_items CspCASL = Just $ symbMapItems csp_casl_keywords

-- lattices (for sublogics) missing

-- CspCASL logic

instance Sentences CspCASL () () CSPSign CSPMorphism () where
  parse_sentence CspCASL = Nothing

instance StaticAnalysis CspCASL Basic_CSP_CASL_C_SPEC () ()
               SYMB_ITEMS SYMB_MAP_ITEMS
               CSPSign CSPMorphism () ()  where
         basic_analysis CspCASL = Just basicAnalysisCspCASLOld
         stat_symb_map_items CspCASL = error "Logic_CspCASL.hs"
         stat_symb_items CspCASL = error "Logic_CspCASL.hs"
         empty_signature CspCASL = emptyCSPSign
         inclusion CspCASL = sigInclusion computeExt isInclusion
         is_subsig CspCASL = isSubSig isInclusion
         signature_union CspCASL s = return . addSig addCSPAddSign s
         signature_difference CspCASL s = return . diffSig diffCSPAddSign s

instance Logic CspCASL ()
               Basic_CSP_CASL_C_SPEC () SYMB_ITEMS SYMB_MAP_ITEMS
               CSPSign
               CSPMorphism
               () () () where

         data_logic CspCASL = Just (Logic CASL)

---- helper ---------------------------------
fun_err :: String -> a
fun_err fname = 
    error $ "*** CspCASL.Logic_CspCASL: Function \"" ++ fname 
              ++ "\" is not yet implemented!"
