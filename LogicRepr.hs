
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
import Set
import Maybe(catMaybes)

-- Simple logic representations (possibly also morphisms via adjointness)

data (Logic id1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1,
      Logic id2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2 
        sign2 morphism2 symbol2 raw_symbol2) =>
  LogicRepr id1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1
            id2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2
     =
     LogicRepr {repr_name :: String,
                source :: id1, source_sublogic :: sublogics1,
                target :: id2, target_sublogic :: sublogics2,
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

comp_repr :: 
     (Logic id1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1,
      Logic id2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2 
        sign2 morphism2 symbol2 raw_symbol2,
      Logic id3 sublogics3
        basic_spec3 sentence3 symb_items3 symb_map_items3 
        sign3 morphism3 symbol3 raw_symbol3
     ) =>
     LogicRepr id1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1
            id2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2

 ->  LogicRepr id2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2
            id3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3

 ->  Maybe (
     LogicRepr id1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1
            id3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 )

comp_repr r1 r2 = if target_sublogic r1 <= source_sublogic r2 then
   Just(LogicRepr{ 
   repr_name = repr_name r1++";"++repr_name r2,
   source = source r1, target = target r2,
   source_sublogic = source_sublogic r1, 
   target_sublogic = target_sublogic r2,
   map_sentence = 
       \si1 se1 -> 
       case map_sign r1 si1 of 
       Nothing -> Nothing
       Just (si2, _) -> 
           case map_sentence r1 si1 se1 of
           Nothing -> Nothing
           Just se2 -> map_sentence r2 si2 se2 ,
   map_sign = 
       \si1 -> 
       case map_sign r1 si1 of 
       Nothing -> Nothing
       Just (si2, se2s) ->   
           case map_sign r2 si2 of
           Nothing -> Nothing
           Just (si3, se3s) -> Just (si3, se3s ++ 
				     catMaybes 
				     (map (map_sentence r2 si2) se2s)) ,

   projection = undefined ,

   map_morphism = \ m1 -> map_morphism r1 m1 >>=  map_morphism r2 ,

   map_symbol = \ s1 -> unionManySets 
		(map (map_symbol r2) (setToList (map_symbol r1 s1)))
   }) else Nothing
