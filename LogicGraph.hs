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
   Add many many logics. (but somewhere else!)

  Jorina:
   aufbauend auf Logic.hs Logik für CASL mit Unterlogiken


   removed instance example for Logic
   (see CASL/Logic_CASL.hs for an example)
   
    Rest alles undefined 
    (no! simply ignore compiler warnings 
    as long proper implementations are missing)

     sublogic_names :: id -> sublogics -> [String] 
                -- the first name is the principal name
           all_sublogics :: id -> [sublogics]
     <=
      meet, join :: l -> l -> l  -- meet = "Durschnitt"
      top :: l


   Weitere Instanzen mit HasCASL, CASL-LTL etc.
    (nur sich selbst als Sublogic)
   Logic-Representations (Sublogic immer = top)

-}

module LogicGraph where

import Logic
import Set
import LogicRepr

-- Existential types for logics and representations

data AnyLogic = forall id sublogics
        basic_spec sentence symb_items symb_map_items
        local_env sign morphism symbol raw_symbol .
        Logic id sublogics
         basic_spec sentence symb_items symb_map_items
         local_env sign morphism symbol raw_symbol =>
        Logic id

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
  Repr(LogicRepr id1 sublogics1 basic_spec1 sentence1 
                 symb_items1 symb_map_items1
                 local_env1 sign1 morphism1 symbol1 raw_symbol1
                 id2 sublogics2 basic_spec2 sentence2 
                 symb_items2 symb_map_items2
                 local_env2 sign2 morphism2 symbol2 raw_symbol2)


{- This does not work due to needed ordering:
instance Functor Set where
  fmap = mapSet
instance Monad Set where
  return = unitSet
  m >>= k          = unionManySets (setToList (fmap k m))
-}

comp_repr :: AnyRepresentation -> AnyRepresentation -> Maybe AnyRepresentation
comp_repr (Repr (r1 :: {-Logic id1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        local_env1 sign1 morphism1 symbol1 raw_symbol1,
        Logic id2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2 
        local_env2 sign2 morphism2 symbol2 raw_symbol2) => -}
        LogicRepr id1 sublogics1 basic_spec1 sentence1 
                symb_items1 symb_map_items1
                local_env1 sign1 morphism1 symbol1 raw_symbol1
            id2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                local_env2 sign2 morphism2 symbol2 raw_symbol2))
  (Repr (r2 :: {-Logic id3 sublogics3
         basic_spec3 sentence3 symb_items3 symb_map_items3
         local_env3 sign3 morphism3 symbol3 raw_symbol3,
         Logic id4 sublogics4
         basic_spec4 sentence4 symb_items4 symb_map_items4 
         local_env4 sign4 morphism4 symbol4 raw_symbol4) => -}
         LogicRepr id3 sublogics3 basic_spec3 sentence3 
	        symb_items3 symb_map_items3
                local_env3 sign3 morphism3 symbol3 raw_symbol3
            id4 sublogics4 basic_spec4 sentence4 symb_items4 symb_map_items4
                local_env4 sign4 morphism4 symbol4 raw_symbol4)) = 
  case coerce (target r1) (source r2) r2 :: Maybe(
	  LogicRepr id2 sublogics2 basic_spec2 sentence2 
                symb_items2 symb_map_items2
                local_env2 sign2 morphism2 symbol2 raw_symbol2
            id4 sublogics4 basic_spec4 sentence4 symb_items4 symb_map_items4
                local_env4 sign4 morphism4 symbol4 raw_symbol4)
		of 
		Nothing -> Nothing
		Just r3 -> case LogicRepr.comp_repr r1 r3 of
			   Nothing -> Nothing
			   Just r4 -> Just (Repr r4)
 
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
  G_morphism id1 id2 
   (LogicRepr id1 sublogics1 basic_spec1 sentence1 
              symb_items1 symb_map_items1
              local_env1 sign1 morphism1 symbol1 raw_symbol1
              id2 sublogics2 basic_spec2 sentence2 
              symb_items2 symb_map_items2
              local_env2 sign2 morphism2 symbol2 raw_symbol2)
   morphism2 

{- 

build these somewhere in a more top-level module

the_logic_list :: [AnyLogic] = [Logic CASL]
		  -- [Logic Prae] -- [Logic CASL, Logic HasCASL, ...]
the_representation_list :: [AnyRepresentation] = []

-}

