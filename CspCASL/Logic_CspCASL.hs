{- |
Module      :  $Id$
Description :  CspCASL instance of type class logic
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

import Logic.Logic

import CASL.AS_Basic_CASL
import CASL.Logic_CASL (CASL(CASL))
import CASL.Morphism
import CASL.Sign
import CASL.SymbolParser

--import CspCASL.AS_CspCASL
import qualified CspCASL.AS_CspCASL as AS_CspCASL
import qualified CspCASL.ATC_CspCASL()
import qualified CspCASL.CspCASL_Keywords as CspCASL_Keywords
import qualified CspCASL.Parse_CspCASL as Parse_CspCASL
import qualified CspCASL.Print_CspCASL ()
import qualified CspCASL.SignCSP as SignCSP
import qualified CspCASL.StatAnaCSP as StatAnaCSP

-- | Lid for CspCASL
data CspCASL = CspCASL deriving (Show)

instance Language CspCASL
    where
      description _ =
        "CspCASL - see\n\n"++
        "http://www.cs.swan.ac.uk/~csmarkus/ProcessesAndData/"

-- | Instance of Category for CspCASL
instance Category CspCASL
    SignCSP.CSPSign         -- signature
    SignCSP.CSPMorphism     -- morphism
    where
      -- ide :: id -> object -> morphism
      ide CspCASL sigma = idMor SignCSP.emptyCSPAddMorphism sigma
      -- o :: id -> morphism -> morphism -> Maybe morphism
      comp CspCASL = compose (const id) -- ??? too simplistic!
      -- dom, cod :: id -> morphism -> object
      dom CspCASL = msource
      cod CspCASL = mtarget
      -- legal_obj :: id -> object -> Bool
      legal_obj CspCASL _ = fun_err "legall_obj"
      -- legal_mor :: id -> morphism -> Bool
      legal_mor CspCASL _ = fun_err "legal_mor"

-- | Instance of Sentences for CspCASL (missing)
instance Sentences CspCASL
    ()                      -- sentence (missing)
    SignCSP.CSPSign         -- signature
    SignCSP.CSPMorphism     -- morphism
    ()                      -- symbol (?)
    where
      parse_sentence CspCASL = Nothing

-- | Syntax of CspCASL
instance Syntax CspCASL
    AS_CspCASL.CspBasicSpec -- basic_spec
    SYMB_ITEMS              -- symb_items
    SYMB_MAP_ITEMS          -- symb_map_items
    where
      parse_basic_spec CspCASL =
          Just Parse_CspCASL.cspBasicSpec
      parse_symb_items CspCASL =
          Just $ symbItems CspCASL_Keywords.csp_casl_keywords
      parse_symb_map_items CspCASL =
          Just $ symbMapItems CspCASL_Keywords.csp_casl_keywords

-- lattices (for sublogics) missing

-- | Instance of Logic for CspCASL
instance Logic CspCASL
    ()                      -- Sublogics (missing)
    AS_CspCASL.CspBasicSpec -- basic_spec
    ()                      -- sentence (missing)
    SYMB_ITEMS              -- symb_items
    SYMB_MAP_ITEMS          -- symb_map_items
    SignCSP.CSPSign         -- signature
    SignCSP.CSPMorphism     -- morphism
    ()                      -- symbol (missing)
    ()                      -- raw_symbol (missing)
    ()                      -- proof_tree (missing)
    where
      stability CspCASL = Experimental
      data_logic CspCASL = Just (Logic CASL)
      empty_proof_tree _ = ()

-- | Static Analysis for CspCASL
instance StaticAnalysis CspCASL
    AS_CspCASL.CspBasicSpec -- basic_spec
    ()                      -- sentence (missing)
    SYMB_ITEMS              -- symb_items
    SYMB_MAP_ITEMS          -- symb_map_items
    SignCSP.CSPSign         -- signature
    SignCSP.CSPMorphism     -- morphism
    ()                      -- symbol (missing)
    ()                      -- raw_symbol (missing)
    where
      basic_analysis CspCASL =
          Just StatAnaCSP.basicAnalysisCspCASL
      stat_symb_map_items CspCASL =
          error "Logic_CspCASL.hs"
      stat_symb_items CspCASL =
          error "Logic_CspCASL.hs"
      empty_signature CspCASL =
          SignCSP.emptyCSPSign
      inclusion CspCASL =
          sigInclusion SignCSP.emptyCSPAddMorphism SignCSP.isInclusion
      is_subsig CspCASL =
          isSubSig SignCSP.isInclusion
      signature_union CspCASL s =
          return . addSig SignCSP.addCspProcSig s
      signature_difference CspCASL s =
          return . diffSig SignCSP.diffCspProcSig s



-- | Helper function for use while CspCASL Logic is work in progress.
fun_err :: String -> a
fun_err fname =
    error $ "*** CspCASL.Logic_CspCASL: Function \"" ++ fname
              ++ "\" is not yet implemented!"

