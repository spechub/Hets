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
import PrettyPrint
import Pretty

data G_basic_spec = forall id sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol .
        Logic id sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol =>
  G_basic_spec id basic_spec 

instance Show G_basic_spec where
    show (G_basic_spec _ s) = show s

instance PrettyPrint G_basic_spec where
    printText0 ga (G_basic_spec _ s) = printText0 ga s

instance Eq G_basic_spec where
  (G_basic_spec i1 s1) == (G_basic_spec i2 s2) =
     coerce i1 i2 s1 == Just s2

data G_sentence = forall id sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol .
        Logic id sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol =>
  G_sentence id sentence 

instance Show G_sentence where
    show (G_sentence _ s) = show s

data G_l_sentence_list = forall id sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol .
        Logic id sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol =>
  G_l_sentence id [(String,sentence)] 

data G_sign = forall id sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol .
        Logic id sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol =>
  G_sign id sign 

instance Show G_sign where
    show (G_sign _ s) = show s

data G_sign_list = forall id sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol .
        Logic id sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol =>
  G_sign_list id [sign] 

data G_symbol = forall id sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol .
        Logic id sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol =>
  G_symbol id symbol 

instance Show G_symbol where
  show (G_symbol _ s) = show s

instance Eq G_symbol where
  (G_symbol i1 s1) == (G_symbol i2 s2) =
     coerce i1 i2 s1 == Just s2

data G_symb_items_list = forall id sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol .
        Logic id sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol =>
        G_symb_items_list id [symb_items] 

instance Show G_symb_items_list where
  show (G_symb_items_list _ l) = show l

instance PrettyPrint G_symb_items_list where
  printText0 ga (G_symb_items_list _ l) = 
      fcat $ punctuate (comma<>space) $ map (printText0 ga) l

instance Eq G_symb_items_list where
  (G_symb_items_list i1 s1) == (G_symb_items_list i2 s2) =
     coerce i1 i2 s1 == Just s2

data G_symb_map_items_list = forall id sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol .
        Logic id sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol =>
        G_symb_map_items_list id [symb_map_items] 

instance Show G_symb_map_items_list where
  show (G_symb_map_items_list _ l) = show l

instance PrettyPrint G_symb_map_items_list where
  printText0 ga (G_symb_map_items_list _ l) = 
      fcat $ punctuate (comma<>space) $ map (printText0 ga) l

instance Eq G_symb_map_items_list where
  (G_symb_map_items_list i1 s1) == (G_symb_map_items_list i2 s2) =
     coerce i1 i2 s1 == Just s2

data G_diagram = forall id sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol .
        Logic id sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol =>
        G_diagram id (Diagram sign morphism) 

data G_sublogics = forall id sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol .
        Logic id sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol =>
        G_sublogics id sublogics 

