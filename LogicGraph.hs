-- needs ghc -fglasgow-exts 

{- HetCATS/LogicGraph.hs
   $Id$
   Till Mossakowski
   
   Assembles all the logics and representations into a graph
   (represented as lists of nodes and edges, using existential
   types).
   The logic graph will be the basis for the Grothendieck logic.

   References:

   T. Mossakowski:
   Relating CASL with Other Specification Languages:
        the Institution Level
   Theoretical Computer Science, July 2003

   Todo:
   Add many many logics.
-}

module LogicGraph where

import Logic
import Dynamic

-- Existential types for logics and representations

data AnyLogic = forall id sublogics
        basic_spec sentence symb_items symb_map_items
        local_env sign morphism symbol raw_symbol .
        Logic id sublogics
         basic_spec sentence symb_items symb_map_items
         local_env sign morphism symbol raw_symbol =>
        Ins id

data AnyRepresentation = forall id1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        local_env1 sign1 morphism1 symbol1 raw_symbol1
        id2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2
        local_env2 sign2 morphism2 symbol2 raw_symbol2 .
      (Logic id1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        local_env1 sign1 morphism1 symbol1 raw_symbol1,
      Logic id2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2 
        local_env2 sign2 morphism2 symbol2 raw_symbol2) =>
  Repr(LogicRepr id1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                     local_env1 sign1 morphism1 symbol1 raw_symbol1
                 id2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                     local_env2 sign2 morphism2 symbol2 raw_symbol2)


--  Composition of representations

coerce :: a -> Maybe b = fromDynamic . toDyn
the = maybe undefined id
g `comp` (Just f) = \x -> f x >>= g

id_repr i s = LogicRepr{ 
  repr_name = "id_"++head (sublogic_names i s),
  source = i, target = i,
  source_sublogic = s, 
  target_sublogic = s,
  map_basic_spec = Just,
  map_sentence = \_ -> Just,
  map_sign = Just,
  projection = Just (proj_sublogic_sign i s,
                     proj_sublogic_morphism i s,
                     proj_sublogic_epsilon i s,
                     proj_sublogic_basic_spec i s,
                     proj_sublogic_symbol i s),
  map_morphism = Just,
  map_symbol = Just
 }

comp_repr :: AnyRepresentation -> AnyRepresentation -> Maybe AnyRepresentation
comp_repr (Repr (r1 :: {-Logic id1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        local_env1 sign1 morphism1 symbol1 raw_symbol1,
        Logic id2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2 
        local_env2 sign2 morphism2 symbol2 raw_symbol2) => -}
        LogicRepr id1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                local_env1 sign1 morphism1 symbol1 raw_symbol1
            id2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                local_env2 sign2 morphism2 symbol2 raw_symbol2))
  (Repr (r2 :: {-Logic id3 sublogics3
         basic_spec3 sentence3 symb_items3 symb_map_items3
         local_env3 sign3 morphism3 symbol3 raw_symbol3,
         Logic id4 sublogics4
         basic_spec4 sentence4 symb_items4 symb_map_items4 
         local_env4 sign4 morphism4 symbol4 raw_symbol4) => -}
         LogicRepr id3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                local_env3 sign3 morphism3 symbol3 raw_symbol3
            id4 sublogics4 basic_spec4 sentence4 symb_items4 symb_map_items4
                local_env4 sign4 morphism4 symbol4 raw_symbol4)) = 
  case coerce (source r2)::Maybe id2 of
  Nothing -> Nothing
  Just _ -> if target_sublogic r1 <= the (coerce (source_sublogic r2)::Maybe sublogics2) then
   Just (Repr (LogicRepr{ 
   repr_name = repr_name r1++";"++repr_name r2,
   source = source r1, target = target r2,
   source_sublogic = source_sublogic r1, 
   target_sublogic = target_sublogic r2,
   map_basic_spec = map_basic_spec r2 `comp` (coerce (map_basic_spec r1)::Maybe(basic_spec1 -> Maybe basic_spec3)),
   map_sentence = 
     ( \sigma -> 
        map_sentence r2 (the (((coerce (map_sign r1 sigma))::Maybe sign3)))
       `comp` (coerce (map_sentence r1 sigma)::Maybe(sentence1 -> Maybe sentence3))),
   map_sign = map_sign r2 `comp` (coerce (map_sign r1)::Maybe(sign1 -> Maybe sign3)),
   projection = undefined {- (proj_sublogic_sign i s,
                      proj_sublogic_morphism i s,
                      proj_sublogic_epsilon i s,
                      proj_sublogic_basic_spec i s,
                      proj_sublogic_symbol i s) -} ,
   map_morphism = map_morphism r2 `comp` (coerce (map_morphism r1)::Maybe(morphism1 -> Maybe morphism3)),
   map_symbol = map_symbol r2 `comp` (coerce (map_symbol r1)::Maybe(symbol1 -> Maybe symbol3))
 }))
                else Nothing


{-
T i_src1 (t1::as_src1->as_tar1) i_tar1) (T i_src2 (t2::as_src2->as_tar2) i_tar2) =
      case    ((Dynamic.fromDynamic (Dynamic.toDyn t2))::Maybe (as_tar1->as_tar2)) of
        Just t -> Just (T i_src1 (t . t1) i_tar2)
        Nothing -> Nothing 

-}

the_logic_list :: [AnyLogic] = []
the_representation_list :: [AnyRepresentation] = []
