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
   J. applied categorical structures 10, 2002, p. 383-402.

   T. Mossakowski: 
   Heterogeneous development graphs and heterogeneous borrowing
   Fossacs 2002, LNCS 2303, p. 326-341

   T. Mossakowski: Foundations of heterogeneous specification
   Submitted

   T. Mossakowski:
   Relating CASL with Other Specification Languages:
        the Institution Level
   Theoretical Computer Science 286, 2002, p. 367-475

   Todo:

-}

module Grothendieck where

import Logic
import LogicRepr
import PrettyPrint
import Pretty
import PPUtils (fsep_latex, comma_latex)

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

    printLatex0 ga (G_basic_spec _ s) = printLatex0 ga s

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
	fsep $ punctuate comma $ map (printText0 ga) l

    printLatex0 ga (G_symb_items_list _ l) = 
	fsep_latex $ punctuate comma_latex $ map (printLatex0 ga) l

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
	fsep $ punctuate comma $ map (printText0 ga) l

    printLatex0 ga (G_symb_map_items_list _ l) = 
	fsep_latex $ punctuate comma_latex $ map (printLatex0 ga) l

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

data G_morphism = forall id sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol .
        Logic id sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol =>
        G_morphism id morphism

g_ide (G_sign id sigma) = G_morphism id (ide id sigma)


-- Existential types for logics and representations

data AnyLogic = forall id sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol .
        Logic id sublogics
         basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol =>
        Logic id

data AnyRepresentation = forall id1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1
        id2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2
        sign2 morphism2 symbol2 raw_symbol2 .
      (Logic id1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1,
      Logic id2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2 
        sign2 morphism2 symbol2 raw_symbol2) =>
  Repr(LogicRepr id1 sublogics1 basic_spec1 sentence1 
                 symb_items1 symb_map_items1
                 sign1 morphism1 symbol1 raw_symbol1
                 id2 sublogics2 basic_spec2 sentence2 
                 symb_items2 symb_map_items2
                 sign2 morphism2 symbol2 raw_symbol2)


type LogicGraph = ([AnyLogic],[AnyRepresentation])

{- This does not work due to needed ordering:
instance Functor Set where
  fmap = mapSet
instance Monad Set where
  return = unitSet
  m >>= k          = unionManySets (setToList (fmap k m))
-}



------------------------------------------------------------------------------
-- The Grothendieck signature category
------------------------------------------------------------------------------

comp_repr :: AnyRepresentation -> AnyRepresentation -> Maybe AnyRepresentation
comp_repr (Repr (r1 :: {-Logic id1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1,
        Logic id2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2 
        sign2 morphism2 symbol2 raw_symbol2) => -}
        LogicRepr id1 sublogics1 basic_spec1 sentence1 
                symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1
            id2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2))
  (Repr (r2 :: {-Logic id3 sublogics3
         basic_spec3 sentence3 symb_items3 symb_map_items3
         sign3 morphism3 symbol3 raw_symbol3,
         Logic id4 sublogics4
         basic_spec4 sentence4 symb_items4 symb_map_items4 
         sign4 morphism4 symbol4 raw_symbol4) => -}
         LogicRepr id3 sublogics3 basic_spec3 sentence3 
	        symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3
            id4 sublogics4 basic_spec4 sentence4 symb_items4 symb_map_items4
                sign4 morphism4 symbol4 raw_symbol4)) = 
  case coerce (target r1) (source r2) r2 :: Maybe(
	  LogicRepr id2 sublogics2 basic_spec2 sentence2 
                symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2
            id4 sublogics4 basic_spec4 sentence4 symb_items4 symb_map_items4
                sign4 morphism4 symbol4 raw_symbol4)
		of 
		Nothing -> Nothing
		Just r3 -> case LogicRepr.comp_repr r1 r3 of
			   Nothing -> Nothing
			   Just r4 -> Just (Repr r4)
 
data GMorphism = forall id1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1
        id2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2 
        sign2 morphism2 symbol2 raw_symbol2 .
      (Logic id1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1,
       Logic id2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2 
        sign2 morphism2 symbol2 raw_symbol2) =>
  GMorphism id1 id2 
   (LogicRepr id1 sublogics1 basic_spec1 sentence1 
              symb_items1 symb_map_items1
              sign1 morphism1 symbol1 raw_symbol1
              id2 sublogics2 basic_spec2 sentence2 
              symb_items2 symb_map_items2
              sign2 morphism2 symbol2 raw_symbol2)
   morphism2 



