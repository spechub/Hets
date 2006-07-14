{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  non-portable (via Logic)

Provides data structures for institution morphisms.
   These are just collections of
   functions between (some of) the types of logics.
-}

{-   References: see Logic.hs

   Todo:
   morphism modifications / representation maps
-}

module Logic.Morphism where

import Logic.Logic
import Logic.Comorphism
import qualified Common.Lib.Set as Set
import Data.Maybe
import Common.DynamicUtils

class (Language cid,
       Logic lid1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
       Logic lid2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2
        sign2 morphism2 symbol2 raw_symbol2 proof_tree2) =>
  Morphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
             | cid -> lid1, cid -> lid2

  where
    -- source and target logic and sublogic
    -- the source sublogic is the maximal one for which the comorphism works
    -- the target sublogic is the resulting one
    morSourceLogic :: cid -> lid1
    morSourceSublogic :: cid -> sublogics1
    morTargetLogic :: cid -> lid2
    morTargetSublogic :: cid -> sublogics2
    -- finer information of target sublogics corresponding to source sublogics
    morMapSublogic :: cid -> sublogics1 -> sublogics2
    -- default implementation
--    morMapSublogic cid _ = targetSublogic cid
    -- the translation functions are partial
    -- because the target may be a sublanguage
    -- map_basic_spec :: cid -> basic_spec1 -> Maybe basic_spec2
    -- we do not cover theoroidal morphisms,
    --   since there are no relevant examples and they do not compose nicely
    -- no mapping of theories, since signatrures and sentences are mapped
    --   contravariantly
    morMap_sign :: cid -> sign1 -> Maybe sign2
    morMap_morphism :: cid -> morphism1 -> Maybe morphism2
    morMap_sentence :: cid -> sign1 -> sentence2 -> Maybe sentence1
          -- also covers semi-morphisms ??
          -- with no sentence translation
          -- - but these are spans!
    morMap_symbol :: cid -> symbol1 -> Set.Set symbol2
    -- morConstituents not needed, because composition only via lax triangles


-- identity morphisms

data IdMorphism lid sublogics =
     IdMorphism lid sublogics deriving Show

idMorphismTc :: TyCon
idMorphismTc = mkTyCon "Logic.Morphism.IdMorphism"

instance Typeable (IdMorphism lid sub) where
  typeOf _ = mkTyConApp idMorphismTc []

instance Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree =>
         Language (IdMorphism lid sublogics) where
           language_name (IdMorphism lid sub) =
               case sublogic_names sub of
               [] -> error "language_name IdMorphism"
               h : _ -> "id_" ++ language_name lid ++ "." ++ h

instance Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree =>
         Morphism (IdMorphism lid sublogics)
          lid sublogics
          basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree
          lid sublogics
          basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree
         where
           morSourceLogic (IdMorphism lid _sub) = lid
           morTargetLogic (IdMorphism lid _sub) = lid
           morSourceSublogic (IdMorphism _lid sub) = sub
           morTargetSublogic (IdMorphism _lid sub) = sub
           morMapSublogic _ _ =
               error "Logic.Morphism.IdMorphism.morMapSublogic"
           morMap_sign _ = Just
           morMap_morphism _ = Just
           morMap_sentence _ = \_ -> Just
           morMap_symbol _ = Set.singleton

-- composition not needed, use lax triangles instead

-- comorphisms inducing morphisms

class Comorphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2 =>
      InducingComorphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
  where
    indMorMap_sign :: cid -> sign2 -> Maybe sign1
    indMorMap_morphism :: cid -> morphism2 -> Maybe morphism1
    epsilon :: cid -> sign2 -> Maybe morphism2
