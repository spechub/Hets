
-- needs ghc -fglasgow-exts -package data

{- HetCATS/LogicRepr.hs
   $Id$
   Till Mossakowski, Christian Maeder
   
   Provides data structures logic representations. 
   Logic representations are just collections of
   functions between (some of) the types of logics.

   References: see Logic.hs

   Todo:
   Weak amalgamability, also for reprs
   repr maps
   reprs out of sublogic relationships
-}

module LogicRepr where

import Logic
import Common.Lib.Set
import Data.Maybe(catMaybes)
import Data.Dynamic

-- Simple logic representations (possibly also morphisms via adjointness)

data (Logic lid1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
      Logic lid2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2 
        sign2 morphism2 symbol2 raw_symbol2 proof_tree2) =>
  LogicRepr lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
     =
     LogicRepr {repr_name :: String,
                source :: lid1, source_sublogic :: sublogics1,
                target :: lid2, target_sublogic :: sublogics2,
                -- the translation functions are partial 
                -- because the target may be a sublanguage
                -- map_basic_spec :: basic_spec1 -> Maybe basic_spec2,
                map_sign :: sign1 -> Maybe (sign2,[sentence2]),
                projection:: Maybe (-- the right adjoint functor Psi
                                    sign2 -> sign1, morphism2 -> morphism1,
                                    -- the counit 
                                    sign2 -> morphism2,
                                    -- basic_spec2 -> basic_spec1,
                                    -- corresponding symbol translation
                                    symbol2 -> Maybe symbol1),  
                map_morphism :: morphism1 -> Maybe morphism2,
                map_sentence :: sign1 -> sentence1 -> Maybe sentence2,
                      -- also covers semi-representations
                      -- with no sentence translation
                map_symbol :: symbol1 -> Set symbol2
                  -- codings may be more complex
               }

instance (Logic lid1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
      Logic lid2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2 
        sign2 morphism2 symbol2 raw_symbol2 proof_tree2) =>
  Typeable (LogicRepr lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2)
  where

instance (Logic lid1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
      Logic lid2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2 
        sign2 morphism2 symbol2 raw_symbol2 proof_tree2) =>
  Eq (LogicRepr lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2)
  where
  r1==r2 = repr_name r1 == repr_name r2 &&
           language_name (source r1) == language_name (source r2) &&
           language_name (target r1) == language_name (target r2) &&
           coerce (source r1) (source r2) (source_sublogic r1) ==
             Just  (source_sublogic r2) &&
           coerce (target r1) (target r2) (target_sublogic r1) ==
             Just  (target_sublogic r2)

instance (Logic lid1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
      Logic lid2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2 
        sign2 morphism2 symbol2 raw_symbol2 proof_tree2) =>
    Show (LogicRepr lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2)
  where
  show r = show (source r) ++ " -> " ++ show (target r)

id_repr :: 
     Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree => 
  lid -> 
    LogicRepr lid sublogics basic_spec sentence symb_items symb_map_items
                  sign morphism symbol raw_symbol proof_tree
              lid sublogics basic_spec sentence symb_items symb_map_items
                  sign morphism symbol raw_symbol proof_tree
id_repr lid = 
     LogicRepr {repr_name = "id_"++language_name lid,
                source = lid, source_sublogic = top,
                target = lid, target_sublogic = top,
                map_sign = \sigma -> Just(sigma,[]),
                projection= Just (-- the right adjoint functor Psi
                                    id, id, 
                                    -- the counit 
                                    ide lid,
                                    -- corresponding symbol translation
                                    Just),  
                map_morphism = Just,
                map_sentence = \_sigma -> Just,
                map_symbol = single
               }

-- composition of logic representations (diagrammatic order)
comp_repr :: 
     (Logic lid1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
      Logic lid2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2 
        sign2 morphism2 symbol2 raw_symbol2 proof_tree2,
      Logic lid3 sublogics3
        basic_spec3 sentence3 symb_items3 symb_map_items3 
        sign3 morphism3 symbol3 raw_symbol3 proof_tree3
     ) =>
     LogicRepr lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2

 ->  LogicRepr lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
            lid3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 proof_tree3

 ->  Maybe (
     LogicRepr lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 proof_tree3 )

comp_repr r1 r2 = if target_sublogic r1 <= source_sublogic r2 then
   Just(LogicRepr{ 
   repr_name = repr_name r1++";"++repr_name r2,
   source = source r1, target = target r2,
   source_sublogic = source_sublogic r1, 
   target_sublogic = target_sublogic r2,
   map_sentence = 
       \si1 se1 -> 
         do (si2,_) <- map_sign r1 si1
            se2 <- map_sentence r1 si1 se1 
            map_sentence r2 si2 se2 ,
   map_sign = 
       \si1 -> 
         do (si2, se2s) <- map_sign r1 si1
            (si3, se3s) <- map_sign r2 si2 
            return (si3, se3s ++ catMaybes 
				  (map (map_sentence r2 si2) se2s)) ,

   projection = undefined ,

   map_morphism = \ m1 -> map_morphism r1 m1 >>=  map_morphism r2 ,

   map_symbol = \ s1 -> unions
		(map (map_symbol r2) (toList (map_symbol r1 s1)))
   }) else Nothing
