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

data AnyLogic = forall id
        basic_spec sentence symb_items symb_map_items anno
        sign morphism symbol raw_symbol .
        Logic id
         basic_spec sentence symb_items symb_map_items anno
         sign morphism symbol raw_symbol =>
        Ins id

data AnyRepresentation = forall id1
        basic_spec1 sentence1 symb_items1 symb_map_items1 anno1
        sign1 morphism1 symbol1 raw_symbol1
        id2
        basic_spec2 sentence2 symb_items2 symb_map_items2 anno2
        sign2 morphism2 symbol2 raw_symbol2 .
      (Logic id1
        basic_spec1 sentence1 symb_items1 symb_map_items1 anno1
        sign1 morphism1 symbol1 raw_symbol1,
      Logic id2
        basic_spec2 sentence2 symb_items2 symb_map_items2 anno2
        sign2 morphism2 symbol2 raw_symbol2) =>
  Repr(LogicRepr id1 basic_spec1 sentence1 symb_items1 symb_map_items1 anno1 sign1 morphism1 symbol1 raw_symbol1
                 id2 basic_spec2 sentence2 symb_items2 symb_map_items2 anno2 sign2 morphism2 symbol2 raw_symbol2)


{-   Composition of representations

data Translation = forall id1 as1 id2 as2 . (Language id1 as1, Language id2 as2) => T id1 (as1->as2) id2

idtrans i = T i id i

comptrans :: AnyRepresentation -> AnyRepresentation -> Maybe AnyRepresentation
comptrans (T i_src1 (t1::as_src1->as_tar1) i_tar1) (T i_src2 (t2::as_src2->as_tar2) i_tar2) =
      case    ((Dynamic.fromDynamic (Dynamic.toDyn t2))::Maybe (as_tar1->as_tar2)) of
        Just t -> Just (T i_src1 (t . t1) i_tar2)
        Nothing -> Nothing 

-}

the_logic_list :: [(String,AnyLogic)] = []
the_representation_list :: [(String,AnyRepresentation)] = []
