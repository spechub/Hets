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

  Jorina:
   aufbauend auf Logic.hs Logik für CASL mit Unterlogiken

   data CASL = CASL
   data CASL_sublogics = CASL_sublogics { has_sub::Bool ...
   instance Logic CASL CASL_sublogics () () () () () () () () where
     logic_name _ = "CASL"
     has_parser _ = False
     has_printer _ = False
     has_analysis _ = False
     map_sen = undefined
   
    Rest alles undefined, bis auf

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

module LogicGraph (module LogicGraph,module Logic_CASL) where

-- exporting the imported Logic instances makes it more easy to access
-- the Logic_ids defined in those modules
import Logic
import Set
import Dynamic
import Logic_CASL

-- The Logic instances needed for the logic list
-- import Logic_CASL

instance Typeable a => Typeable (Set a) where
  typeOf t = mkAppTy (mkTyCon "Set") [typeOf t]
  

-- Existential types for logics and representations

data AnyLogic = forall id sublogics
        basic_spec sentence symb_items_list symb_map_items_list
        local_env sign morphism symbol raw_symbol .
        Logic id sublogics
         basic_spec sentence symb_items_list symb_map_items_list
         local_env sign morphism symbol raw_symbol =>
        Logic id

data AnyRepresentation = forall id1 sublogics1
        basic_spec1 sentence1 symb_items_list1 symb_map_items_list1
        local_env1 sign1 morphism1 symbol1 raw_symbol1
        id2 sublogics2
        basic_spec2 sentence2 symb_items_list2 symb_map_items_list2
        local_env2 sign2 morphism2 symbol2 raw_symbol2 .
      (Logic id1 sublogics1
        basic_spec1 sentence1 symb_items_list1 symb_map_items_list1
        local_env1 sign1 morphism1 symbol1 raw_symbol1,
      Logic id2 sublogics2
        basic_spec2 sentence2 symb_items_list2 symb_map_items_list2 
        local_env2 sign2 morphism2 symbol2 raw_symbol2) =>
  Repr(LogicRepr id1 sublogics1 basic_spec1 sentence1 
                 symb_items_list1 symb_map_items_list1
                 local_env1 sign1 morphism1 symbol1 raw_symbol1
                 id2 sublogics2 basic_spec2 sentence2 
                 symb_items_list2 symb_map_items_list2
                 local_env2 sign2 morphism2 symbol2 raw_symbol2)


--  Composition of representations

coerce :: a -> Maybe b = fromDynamic . toDyn
the = maybe undefined id
g `comp` (Just f) = \x -> f x >>= g

{- This does not work due to needed ordering:
instance Functor Set where
  fmap = mapSet
instance Monad Set where
  return = unitSet
  m >>= k          = unionManySets (setToList (fmap k m))
-}
g `compSet` (Just f) = \x -> unionManySets (map g (setToList (f x)))

id_repr i s = LogicRepr{ 
  repr_name = "id_"++head (sublogic_names i s),
  source = i, target = i,
  source_sublogic = s, 
  target_sublogic = s,
--  map_basic_spec = Just,
  map_sentence = \_ -> Just,
  map_sign = \sigma -> Just (sigma,[]),
  projection = Just (proj_sublogic_sign i s,
                     proj_sublogic_morphism i s,
                     proj_sublogic_epsilon i s,
                     -- proj_sublogic_basic_spec i s,
                     proj_sublogic_symbol i s),
  map_morphism = Just,
  map_symbol = \x -> unitSet x
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
   -- map_basic_spec = map_basic_spec r2 `comp` (coerce (map_basic_spec r1)::Maybe(basic_spec1 -> Maybe basic_spec3)),
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
   map_symbol = map_symbol r2 `compSet` (coerce (map_symbol r1)::Maybe(symbol1 -> Set symbol3))
 }))
                else Nothing

the_logic_list :: [AnyLogic] = [Logic CASL]
		  -- [Logic Prae] -- [Logic CASL, Logic HasCASL, ...]
the_representation_list :: [AnyRepresentation] = []


