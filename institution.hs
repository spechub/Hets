-- needs ghc -fglasgow-exts 

module Institution where

-- maps and sets, just a quick thing
type Set a = [a]
type Map a = [(a,a)]

-- diagrams, nodes are just integers
type Node = Int
type Edge morphism = (Node,morphism,Node)
data Diagram object morphism = Diagram [(Node,object)] [Edge morphism] 
empty_diagram :: Diagram o m
empty_diagram = Diagram [] []
add_node :: Diagram o m -> o -> (Node,Diagram o m)
add_node (Diagram nodes edges) obj = 
         (node,Diagram ((node,obj):nodes) edges) where
            node = maximum (map fst nodes)
add_edge :: Diagram o m -> Edge m -> Diagram o m
add_edge (Diagram nodes edges) edge =
         Diagram nodes (edge:edges)
object_at_node :: Node -> Diagram o m -> Maybe (Node,o)
object_at_node node (Diagram nodes edges) =
         case lookup node nodes of
           Just obj -> Just (node,obj)
           Nothing -> Nothing
diagram_nodes :: Diagram o m  -> [(Node,o)]
diagram_nodes (Diagram nodes edges) = nodes
diagram_edges :: Diagram o m -> [Edge m]
diagram_edges (Diagram nodes edges) = edges

-- identifiers, fixed for all institutions
data ID = Simple_Id String
        | Compound_Id (String,[ID])

-- Categories are given by a quotient,
-- i.e. we need equality
-- Should we allow arbitrary composition graphs and build paths?
class (Eq object, Eq morphism) => 
      Category id object morphism | id ->, id -> morphism where
         ide :: id -> object -> morphism
         o :: id -> morphism -> morphism -> Maybe morphism
         dom, cod :: id -> morphism -> object
         legal_obj :: id -> object -> Bool
         legal_mor :: id -> morphism -> Bool

-- abstract syntax, parsing and printing
class (Read basic_spec, Read formula, Read symb_items, 
       Read symb_map_items, Read anno,
       Show basic_spec, Show formula, Show symb_items, 
       Show symb_map_items, Show anno) =>
      Syntax basic_spec formula symb_items symb_map_items anno

class (Syntax basic_spec formula symb_items symb_map_items anno,
       Show sign, Show morphism, Show symbol, Show raw_symbol,
       Ord symbol, --  needed for efficient symbol tables
       Category id sign morphism) =>
      Institution id
        basic_spec formula symb_items symb_map_items anno
        sign morphism symbol raw_symbol 
        | id -> basic_spec, id -> formula, id -> symb_items,
          id -> symb_map_items, id -> anno,
          id -> sign, id -> morphism, id ->symbol, id -> raw_symbol
       where

         -- static analysis of basic specifications and symbol maps
         basic_analysis :: id -> 
                           (basic_spec,sign,[anno]) -> 
                           (sign,[(String,formula)])
         stat_symb_map_items :: id -> [symb_map_items] -> Map raw_symbol
         stat_symb_items :: id -> [symb_items] -> [raw_symbol] 

         -- architectural sharing analysis for one morphism
         ensures_amalgamability :: id ->
              (Diagram sign morphism, Node, sign, Edge morphism, morphism) -> 
               Diagram sign morphism
         -- do we need it also for sinks consisting of two morphisms?

         -- symbols and symbol maps
         symbol_to_raw :: id -> symbol -> raw_symbol
         id_to_raw :: id -> ID -> raw_symbol 
         sym_of :: id -> sign -> Set symbol
         symmap_of :: id -> morphism -> Map symbol
         matches :: id -> symbol -> raw_symbol -> Bool
         name :: id -> symbol -> ID 
   
         -- operations on signatures and morphisms
         empty_signature :: id -> sign
         signature_union :: id -> sign -> sign -> sign
         final_union :: id -> sign -> sign -> sign
         is_subsig :: id -> sign -> sign -> Bool
         generated_sign, cogenerated_sign :: id -> [raw_symbol] -> sign -> morphism
         induced_from_morphism :: id -> Map raw_symbol -> sign -> morphism
         induced_from_to_morphism :: id -> Map raw_symbol -> sign -> sign -> morphism 

         -- derived operations, need not to be given

         -- parsing, printing, accessible via institution identity
         read_basic_spec :: id -> String -> basic_spec
         read_formula :: id -> String -> formula
         read_symb_items :: id -> String -> symb_items
         read_symb_map_items :: id -> String -> symb_map_items
         read_anno :: id -> String -> anno

         read_basic_spec _ = read
         read_formula _ = read
         read_symb_items _ = read
         read_symb_map_items _ = read
         read_anno _ = read
 
         show_basic_spec :: id -> basic_spec -> String
         show_formula :: id -> formula -> String
         show_symb_items :: id -> symb_items -> String
         show_symb_map_items :: id -> symb_map_items -> String
         show_anno :: id -> anno -> String
         show_sign :: id -> sign -> String
         show_morphism :: id -> morphism -> String
         show_symbol :: id -> symbol -> String
         show_raw_symbol :: id -> raw_symbol -> String 

         show_basic_spec _ = show
         show_formula _ = show
         show_symb_items _ = show
         show_symb_map_items _ = show
         show_anno _ = show
         show_sign _ = show
         show_morphism _ = show
         show_symbol _ = show
         show_raw_symbol _ = show

-- Simple institution representations (possibly also morphisms via adjointness)

data (Institution id1
        basic_spec1 formula1 symb_items1 symb_map_items1 anno1
        sign1 morphism1 symbol1 raw_symbol1,
      Institution id2
        basic_spec2 formula2 symb_items2 symb_map_items2 anno2
        sign2 morphism2 symbol2 raw_symbol2) =>
  InstRepr id1 basic_spec1 formula1 symb_items1 symb_map_items1 anno1 sign1 morphism1 symbol1 raw_symbol1
           id2 basic_spec2 formula2 symb_items2 symb_map_items2 anno2 sign2 morphism2 symbol2 raw_symbol2
     =
     InstRepr {map_basic_spec :: basic_spec1->basic_spec2,
               map_formula :: sign1 -> formula1 -> formula2,
               map_anno :: anno1 -> anno2,
               map_sign :: sign1 -> sign2,
               project_sign :: Maybe (sign2 -> sign1,morphism2),  -- right adjoint and counit
               map_morphism :: morphism1 -> morphism2,
               map_symbol :: symbol1 -> symbol2
               }

-- The Grothendieck institution
data Grothendieck = Grothendieck

data G_basic_spec = forall id
        basic_spec formula symb_items symb_map_items anno
        sign morphism symbol raw_symbol .
        Institution id
         basic_spec formula symb_items symb_map_items anno
         sign morphism symbol raw_symbol =>
        G_basic_spec basic_spec

data G_formula = forall id
        basic_spec formula symb_items symb_map_items anno
        sign morphism symbol raw_symbol .
        Institution id
         basic_spec formula symb_items symb_map_items anno
         sign morphism symbol raw_symbol =>
        G_formula formula

data G_anno = forall id
        basic_spec formula symb_items symb_map_items anno
        sign morphism symbol raw_symbol .
        Institution id
         basic_spec formula symb_items symb_map_items anno
         sign morphism symbol raw_symbol =>
        G_anno anno

data G_sign = forall id
        basic_spec formula symb_items symb_map_items anno
        sign morphism symbol raw_symbol .
        Institution id
         basic_spec formula symb_items symb_map_items anno
         sign morphism symbol raw_symbol =>
        G_sign sign

data G_morphism = forall id
        basic_spec formula symb_items symb_map_items anno
        sign morphism symbol raw_symbol .
        Institution id
         basic_spec formula symb_items symb_map_items anno
         sign morphism symbol raw_symbol =>
        G_morphism morphism

data G_symbol = forall id
        basic_spec formula symb_items symb_map_items anno
        sign morphism symbol raw_symbol .
        Institution id
         basic_spec formula symb_items symb_map_items anno
         sign morphism symbol raw_symbol =>
        G_symbol symbol

