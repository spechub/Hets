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


data Grothendieck = Grothendieck

data G_basic_spec = forall id
        basic_spec sentence symb_items symb_map_items anno
        sign morphism symbol raw_symbol .
        Logic id
         basic_spec sentence symb_items symb_map_items anno
         sign morphism symbol raw_symbol =>
        G_basic_spec basic_spec

data G_sentence = forall id
        basic_spec sentence symb_items symb_map_items anno
        sign morphism symbol raw_symbol .
        Logic id
         basic_spec sentence symb_items symb_map_items anno
         sign morphism symbol raw_symbol =>
        G_sentence sentence

data G_anno = forall id
        basic_spec sentence symb_items symb_map_items anno
        sign morphism symbol raw_symbol .
        Logic id
         basic_spec sentence symb_items symb_map_items anno
         sign morphism symbol raw_symbol =>
        G_anno anno

data G_sign = forall id
        basic_spec sentence symb_items symb_map_items anno
        sign morphism symbol raw_symbol .
        Logic id
         basic_spec sentence symb_items symb_map_items anno
         sign morphism symbol raw_symbol =>
        G_sign sign

data G_morphism = forall id
        basic_spec sentence symb_items symb_map_items anno
        sign morphism symbol raw_symbol .
        Logic id
         basic_spec sentence symb_items symb_map_items anno
         sign morphism symbol raw_symbol =>
        G_morphism morphism

data G_symbol = forall id
        basic_spec sentence symb_items symb_map_items anno
        sign morphism symbol raw_symbol .
        Logic id
         basic_spec sentence symb_items symb_map_items anno
         sign morphism symbol raw_symbol =>
        G_symbol symbol


