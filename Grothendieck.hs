-- needs ghc -fglasgow-exts 

{- HetCATS/Grothendieck.hs
   $Id$
   Till Mossakowski
   
   The Grothendieck logic is defined to be the
   heterogeneous logic over the logic graph.
   This will be the logic over which the data 
   structures and algorithms for specification in-the-large
   are built.

   References:

   R. Diaconescu:
   Grothendieck institutions
   J. applied categorical structures, to appear

   T. Mossakowski: 
   Heterogeneous development graphs and heterogeneous borrowing
   Fossacs 2002, LNCS 2303

   T. Mossakowski: Simplified heterogeneous specification
   Submitted

   Todo:

-}

module Grothendieck where

import Logic
import LogicGraph
import Dynamic

data Grothendieck = Grothendieck

data G_basic_spec = forall id sublogics
        basic_spec sentence symb_items symb_map_items
        local_env sign morphism symbol raw_symbol .
        Logic id sublogics
         basic_spec sentence symb_items symb_map_items
         local_env sign morphism symbol raw_symbol =>
        G_basic_spec id basic_spec

data G_sentence = forall id sublogics
        basic_spec sentence symb_items symb_map_items
        local_env sign morphism symbol raw_symbol .
        Logic id sublogics
         basic_spec sentence symb_items symb_map_items
         local_env sign morphism symbol raw_symbol =>
        G_sentence id sentence

data G_l_sentence_list = forall id sublogics
        basic_spec sentence symb_items symb_map_items
        local_env sign morphism symbol raw_symbol .
        Logic id sublogics
         basic_spec sentence symb_items symb_map_items
         local_env sign morphism symbol raw_symbol =>
        G_l_sentence id [(String,sentence)]

data G_sign = forall id sublogics
        basic_spec sentence symb_items symb_map_items
        local_env sign morphism symbol raw_symbol .
        Logic id sublogics
         basic_spec sentence symb_items symb_map_items
         local_env sign morphism symbol raw_symbol =>
        G_sign id sign

data G_sign_list = forall id sublogics
        basic_spec sentence symb_items symb_map_items
        local_env sign morphism symbol raw_symbol .
        Logic id sublogics
         basic_spec sentence symb_items symb_map_items
         local_env sign morphism symbol raw_symbol =>
        G_sign_list id [sign]

data G_local_env = forall id sublogics
        basic_spec sentence symb_items symb_map_items
        local_env sign morphism symbol raw_symbol .
        Logic id sublogics
         basic_spec sentence symb_items symb_map_items
         local_env sign morphism symbol raw_symbol =>
        G_local_env id local_env

data G_morphism = forall id1 sublogics1
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
  G_morphism 
   id1
   id2 
   (LogicRepr id1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                  local_env1 sign1 morphism1 symbol1 raw_symbol1
              id2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                  local_env2 sign2 morphism2 symbol2 raw_symbol2)
   morphism2

data G_symbol = forall id sublogics
        basic_spec sentence symb_items symb_map_items
        local_env sign morphism symbol raw_symbol .
        Logic id sublogics
         basic_spec sentence symb_items symb_map_items
         local_env sign morphism symbol raw_symbol =>
        G_symbol id symbol

data G_symb_items = forall id sublogics
        basic_spec sentence symb_items symb_map_items
        local_env sign morphism symbol raw_symbol .
        Logic id sublogics
         basic_spec sentence symb_items symb_map_items
         local_env sign morphism symbol raw_symbol =>
        G_symb_items id symb_items

data G_symb_items_list = forall id sublogics
        basic_spec sentence symb_items symb_map_items
        local_env sign morphism symbol raw_symbol .
        Logic id sublogics
         basic_spec sentence symb_items symb_map_items
         local_env sign morphism symbol raw_symbol =>
        G_symb_items_list id [symb_items]

data G_symb_map_items = forall id sublogics
        basic_spec sentence symb_items symb_map_items
        local_env sign morphism symbol raw_symbol .
        Logic id sublogics
         basic_spec sentence symb_items symb_map_items
         local_env sign morphism symbol raw_symbol =>
        G_symb_map_items id symb_map_items

data G_symb_map_items_list = forall id sublogics
        basic_spec sentence symb_items symb_map_items
        local_env sign morphism symbol raw_symbol .
        Logic id sublogics
         basic_spec sentence symb_items symb_map_items
         local_env sign morphism symbol raw_symbol =>
        G_symb_map_items_list id [symb_map_items]

data G_diagram = forall id sublogics
        basic_spec sentence symb_items symb_map_items
        local_env sign morphism symbol raw_symbol .
        Logic id sublogics
         basic_spec sentence symb_items symb_map_items
         local_env sign morphism symbol raw_symbol =>
        G_diagram id (Diagram sign morphism)

homogenize_symb_items :: [G_symb_items] -> Maybe G_symb_items_list
homogenize_symb_items [] = Nothing
homogenize_symb_items (G_symb_items i (s::symb_map_items) : rest) = 
  maybe Nothing 
        (\l -> Just (G_symb_items_list i l))  
        ( sequence (Just s : 
                    map (\(G_symb_items _ si) -> coerce si::Maybe symb_map_items) rest) )
