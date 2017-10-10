{-# LANGUAGE MultiParamTypeClasses #-}
{- |
Module      :  ./HPL/Logic_HPL.hs
Description :  Instance of class Logic for hybrid propositional logic H'PL
Copyright   :  (c) Mihai Codescu, IMAR, 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mscodescu@gmail.com
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Instance of class Logic for the hybrid propositional logic H'PL:
   - quantifier-free
   - only one binary modality
-}

{-
  Ref.

  Encoding hybridized institutions into first-order logic
  R Diaconescu, A Madeira
  Mathematical Structures in Computer Science 26 (5), 745-788
-}

module HPL.Logic_HPL where

import Logic.Logic

import HPL.ATC_HPL ()
import Propositional.ATC_Propositional ()

import HPL.Sign
import HPL.Morphism
--import HPL.Sublogic
import HPL.Symbol
import HPL.AS_BASIC_HPL
import HPL.Parse_AS_Basic
import HPL.Analysis
import qualified Propositional.AS_BASIC_Propositional as PBasic

import qualified Data.Map as Map

{-
import Common.ProverTools
import Common.Consistency
import Common.()
import Common.Id


import Data.Monoid
-} 

-- | Lid for hybrid propositional logic
data HPL = HPL deriving Show

instance Language HPL where
    description _ = "Hybrid propositional logic"
       
-- | Instance of Category for propositional logic
instance Category HSign HMorphism where
    -- Identity morhpism
    ide = idMor
    -- Returns the domain of a morphism
    dom = source
    -- Returns the codomain of a morphism
    cod = target
    -- check if morphism is inclusion
    isInclusion m = Map.null (propMap m) && Map.null (nomMap m)
    -- tests if the morphism is ok
    legal_mor = isLegalMorphism
    -- composition of morphisms
    composeMorphisms = composeMor

-- | Instance of Sentences for propositional logic
instance Sentences HPL FORMULA
    HSign HMorphism Symbol where
    negation HPL = error "negation in HPL nyi" -- Just . negForm nullRange
    -- returns the set of symbols
    sym_of HPL = singletonList . symOf
    -- returns the symbol map
    symmap_of HPL = getSymbolMap
    -- returns the name of a symbol
    sym_name HPL = getSymbolName
    symKind HPL = symKindStr
    -- translation of sentences along signature morphism
    map_sen HPL = error "map sentence in HPL nyi" --mapSentence TODO in Morphism.hs
    -- there is nothing to leave out
    --simplify_sen HPL _ = error "simplify sentences in HPL nyi" --simplify

instance Monoid BASIC_SPEC where
    mempty = Basic_spec []
    mappend (Basic_spec l1) (Basic_spec l2) = Basic_spec $ l1 ++ l2 --TODO: where is this needed?

-- - | Syntax of HPL logic
instance Syntax HPL BASIC_SPEC
    Symbol PBasic.SYMB_ITEMS PBasic.SYMB_MAP_ITEMS where
         parsersAndPrinters HPL =
           addSyntax "Hets" (basicSpec, pretty)
           $ makeDefault (basicSpec, pretty)
         parse_symb_items HPL = Just symbItems
         parse_symb_map_items HPL = Just symbMapItems

-- | Instance of Logic for propositional logc
instance Logic HPL
    ()                    -- Sublogics
    BASIC_SPEC                -- basic_spec
    FORMULA                   -- sentence
    PBasic.SYMB_ITEMS                -- symb_items
    PBasic.SYMB_MAP_ITEMS            -- symb_map_items
    HSign                          -- sign
    HMorphism                  -- morphism
    Symbol                      -- symbol
    Symbol                      -- raw_symbol
    ()                      -- proof_tree
    where
        -- hybridization
      parse_basic_sen HPL = Just $ const impFormula
      stability HPL = Experimental
      top_sublogic HPL = ()
      all_sublogics HPL = [()]
      empty_proof_tree HPL = ()
    -- supplied provers
      provers HPL = []
      cons_checkers HPL = []
      conservativityCheck HPL = []

-- | Static Analysis for propositional logic
instance StaticAnalysis HPL
    BASIC_SPEC                -- basic_spec
    FORMULA                   -- sentence
    PBasic.SYMB_ITEMS                -- symb_items
    PBasic.SYMB_MAP_ITEMS            -- symb_map_items
    HSign                          -- sign
    HMorphism                  -- morphism
    Symbol                      -- symbol
    Symbol                      -- raw_symbol
        where
          basic_analysis HPL =
             Just basicHPLAnalysis
          sen_analysis HPL = error "nyi" -- Just pROPsen_analysis
          empty_signature HPL =  emptySig
          is_subsig HPL = isSubSigOf
          subsig_inclusion HPL s = return . inclusionMap s
          signature_union HPL = sigUnion
          symbol_to_raw HPL = symbolToRaw
          id_to_raw HPL = error "id_to_raw in HPL nyi" --idToRaw
          matches HPL = error "nyi" --Symbol.matches
          stat_symb_items HPL _ = error "nyi" --mkStatSymbItems
          stat_symb_map_items HPL _ _ = error "nyi" --mkStatSymbMapItem
          morphism_union HPL = error "nyi" --morphismUnion
          induced_from_morphism HPL = error "nyi" --inducedFromMorphism
          induced_from_to_morphism HPL = error "nyi" --inducedFromToMorphism
          signature_colimit HPL = error "nyi" --signatureColimit

{-
-- | Sublogics
--instance SemiLatticeWithTop () where
--    lub = error "nyi"
--    top = error "nyi"

instance MinSublogic () BASIC_SPEC where
     minSublogic = error "nyi"

instance MinSublogic () HSign where
    minSublogic = error "nyi"

--instance SublogicName () where
--    sublogicName = error "nyi"

instance MinSublogic () FORMULA where
    minSublogic = error "nyi"

instance MinSublogic () Symbol where
    minSublogic = error "nyi"

instance MinSublogic () PBasic.SYMB_ITEMS where
    minSublogic = error "nyi"

instance MinSublogic () HMorphism where
    minSublogic = error "nyi"

instance MinSublogic () PBasic.SYMB_MAP_ITEMS where
    minSublogic = error "nyi"

instance ProjectSublogicM () Symbol where
    projectSublogicM = error "nyi"

instance ProjectSublogic () HSign where
    projectSublogic = error "nyi"

instance ProjectSublogic () HMorphism where
    projectSublogic = error "nyi"

instance ProjectSublogicM () PBasic.SYMB_MAP_ITEMS where
    projectSublogicM = error "nyi"

instance ProjectSublogicM () PBasic.SYMB_ITEMS where
    projectSublogicM = error "nyi"

instance ProjectSublogic () BASIC_SPEC where
    projectSublogic = error "nyi"

instance ProjectSublogicM () FORMULA where
    projectSublogicM = error "nyi"
-}

