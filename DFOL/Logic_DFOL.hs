{- |
Module      :  $Header$
Description :  Instances of classes defined in Logic.hs for first-order logic
               with dependent types (DFOL)
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable

Ref: Florian Rabe: First-Order Logic with Dependent Types.
     IJCAR 2006, pages 377-391.
-}

module DFOL.Logic_DFOL where

import DFOL.AS_DFOL
import DFOL.Sign
import DFOL.Morphism
import DFOL.Parse_AS_DFOL
import DFOL.ATC_DFOL ()
import DFOL.Analysis_DFOL
import DFOL.Symbol
import DFOL.Colimit
import Logic.Logic
import Common.Result
import qualified Data.Map as Map
import qualified Data.Set as Set

-- lid for first-order logic with dependent types
data DFOL = DFOL deriving Show

instance Language DFOL where
   description _ = "First-Order Logic with Dependent Types\n"
                   ++ "developed by F. Rabe"

-- instance of Category for DFOL
instance Category Sign Morphism where
   ide = idMorph
   dom = source
   cod = target
   isInclusion = Map.null . symMap . morphCanForm
   composeMorphisms = compMorph
   legal_mor = isValidMorph

-- syntax for DFOL
instance Syntax DFOL BASIC_SPEC SYMB_ITEMS SYMB_MAP_ITEMS where
   parse_basic_spec DFOL = Just basicSpec
   parse_symb_items DFOL = Just symbItems
   parse_symb_map_items DFOL = Just symbMapItems

-- sentences for DFOL
instance Sentences DFOL FORMULA Sign Morphism Symbol where
   map_sen DFOL m = wrapInResult . (applyMorph m)
   sym_of DFOL = (Set.map Symbol) . getSymbols
   symmap_of DFOL = toSymMap . symMap
   sym_name DFOL = toId

-- static analysis for DFOL
instance StaticAnalysis DFOL
   BASIC_SPEC
   FORMULA
   SYMB_ITEMS
   SYMB_MAP_ITEMS
   Sign
   Morphism
   Symbol
   Symbol
   where
   basic_analysis DFOL = Just basicAnalysis
   stat_symb_map_items DFOL = symbMapAnalysis
   stat_symb_items DFOL = symbAnalysis
   symbol_to_raw DFOL = id
   id_to_raw DFOL = fromId
   matches DFOL s1 s2 = s1 == s2
   empty_signature DFOL = emptySig
   is_subsig DFOL sig1 sig2 = isValidMorph $ Morphism sig1 sig2 $ Map.empty
   signature_union DFOL = sigUnion
   intersection DFOL = sigIntersection
   subsig_inclusion DFOL =  inclusionMorph
   morphism_union DFOL = morphUnion
   induced_from_morphism DFOL = inducedFromMorphism
   induced_from_to_morphism DFOL = inducedFromToMorphism
   signature_colimit DFOL = sigColimit
   generated_sign DFOL = coGenSig False
   cogenerated_sign DFOL = coGenSig True

-- instance of logic for DFOL
instance Logic DFOL
   ()
   BASIC_SPEC
   FORMULA
   SYMB_ITEMS
   SYMB_MAP_ITEMS
   Sign
   Morphism
   Symbol
   Symbol
   ()

-- creates a Result
wrapInResult :: a -> Result a
wrapInResult x = Result [] $ Just x
