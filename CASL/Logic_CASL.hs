
{- HetCATS/CASL/Logic_CASL.hs
   $Id$
   Authors: Klaus Lüttich
   Year:    2002

   Here is the place where the class Logic is instantiated for CASL.
   Also the instances for Syntax an Category.

   todo:
     - writing real functions

-}

module Logic_CASL where

import AS_Basic_CASL
import Print_AS_Basic
import Parse_AS_Basic

import LocalEnv
import Logic

import Error
import Dynamic
import qualified Sublogics

-- a dummy datatype for the LogicGraph and for identifying the right
-- instances
data CASL = CASL 
	    deriving (Show)

instance Category CASL Sign String -- morphism 
    where
         -- ide :: id -> object -> morphism
	 ide CASL _ = fun_err "ide"
         -- o :: id -> morphism -> morphism -> Maybe morphism
	 o CASL _ _ = fun_err "o"
         -- dom, cod :: id -> morphism -> object
	 dom CASL _ = fun_err "dom"
	 cod CASL _ = fun_err "cod"
         -- legal_obj :: id -> object -> Bool
	 legal_obj CASL _ = fun_err "legall_obj"
         -- legal_mor :: id -> morphism -> Bool
	 legal_mor CASL _ = fun_err "legal_mor"


-- abstract syntax, parsing and printing

instance Syntax CASL BASIC_SPEC 
                Sentence
		SYMB_ITEMS_LIST SYMB_MAP_ITEMS_LIST
      where 
         parse_basic_spec CASL = basicSpec
{-	 parse_symb_items_list CASL = fun_err "parse_symb_items_list"
	 parse_symb_map_items_list CASL = fun_err "parse_symb_map_items_list"
-}
data CASL_sublogics = CASL_ deriving (Show,Eq,Ord)

instance Typeable Sublogics.CASL_Sublogics where
    typeOf (Sublogics.CASL_SL _ _ _ _ _ _) = mkAppTy (mkTyCon "CASL_SL") []

-- lattices (for sublogics)

instance LatticeWithTop Sublogics.CASL_Sublogics where
    -- meet, join :: l -> l -> l
    meet = Sublogics.sublogics_min
    join = Sublogics.sublogics_max
    -- top :: l
    top = Sublogics.top

-- CASL logic

{- class (Syntax id basic_spec sentence symb_items_list symb_map_items_list,
       Show sign, Show morphism, Show symbol, Show raw_symbol,
       Ord symbol, --  needed for efficient symbol tables
       Eq raw_symbol,
       Category id sign morphism,
       LatticeWithTop sublogics,
       -- needed for heterogeneous coercions:
       Typeable id, Typeable sublogics, Typeable sign, Typeable morphism, 
       Typeable symbol, Typeable raw_symbol,
       Typeable basic_spec, Typeable sentence, Typeable symb_items_list, 
       Typeable symb_map_items_list) =>
-}
instance Logic CASL Sublogics.CASL_Sublogics
               BASIC_SPEC Sentence SYMB_ITEMS_LIST SYMB_MAP_ITEMS_LIST
	       LocalEnv Sign 
	       String -- morphism 
	       Symbol RawSymbol 
       where
         logic_name CASL   = "CASL"
         has_parser CASL   = False
	 has_printer CASL  = False
         has_analysis CASL = False

         -- sentence translation
         -- map_sen :: id -> morphism -> sentence -> Result sentence
	 map_sen CASL _ _ = fun_err "map_sen"
         -- parsing of sentences
         -- parse_sentence :: id -> local_env -> String -> Result sentence
	 parse_sentence CASL _ _ = fun_err "parse_sentence"
           -- is a term parser needed as well?

         -- static analysis of basic specifications and symbol maps
         {-basic_analysis :: id -> 
                           (basic_spec,  -- abstract syntax tree
                            local_env,   -- efficient table for env signature
                            [Annotation]) ->   -- global annotations
                           Result (local_env,sign,[(String,sentence)])
                              -- the output local env is expected to be
                              -- just the input local env, united with the sign.
                              -- We have both just for efficiency reasons.
                              -- These include any new annotations-}
	 basic_analysis CASL _ = fun_err "basic_analysis"
         {- stat_symb_map_items_list :: 
	    id -> [symb_map_items_list] -> Result (EndoMap raw_symbol) -}
{-	 stat_symb_map_items_list CASL _ = fun_err "stat_symb_map_items_list"
         {- stat_symb_items_list :: 
	    id -> [symb_items_list] -> Result [raw_symbol] -}
	 stat_symb_items_list CASL _ = fun_err "stat_symb_items_list"

         -- architectural sharing analysis for one morphism
         -- ensures_amalgamability :: id ->
         --   (Diagram sign morphism, Node, sign, LEdge morphism, morphism) -> 
         --    Result (Diagram sign morphism)
	 ensures_amalgamability CASL _ = fun_err "ensures_amalgamability"
         -- do we need it also for sinks consisting of two morphisms?

         -- symbols and symbol maps
         -- symbol_to_raw :: id -> symbol -> raw_symbol
         symbol_to_raw CASL _ = fun_err "symbol_to_raw"
         -- id_to_raw :: id -> Id -> raw_symbol 
         id_to_raw CASL _ = fun_err "id_to_raw"
         -- sym_of :: id -> sign -> Set symbol
         sym_of CASL _ = fun_err "sym_of"
         -- symmap_of :: id -> morphism -> EndoMap symbol
         symmap_of CASL _ = fun_err "symmap_of"
         -- matches :: id -> symbol -> raw_symbol -> Bool
         matches CASL _ _ = fun_err "matches"
         -- sym_name :: id -> symbol -> Id 
         sym_name CASL _ = fun_err "sym_name"
   
         -- operations on local envs, signatures and morphisms
         -- empty_local_env :: local_env
         empty_local_env = fun_err "empty_local_env"
         -- add_sign :: sign -> local_env -> local_env
         add_sign _ _ = fun_err "add_sign"
         -- empty_signature :: id -> sign
         empty_signature CASL = fun_err "empty_signature"
         -- signature_union :: id -> sign -> sign -> Result sign
         signature_union CASL _ _ = fun_err "signature_union"
         -- final_union :: id -> sign -> sign -> Result sign
         final_union CASL _ _ = fun_err "final_union"
         -- is_subsig :: id -> sign -> sign -> Bool
         is_subsig CASL _ _ = fun_err "is_subsig"
         -- generated_sign, cogenerated_sign :: id -> [raw_symbol] -> sign -> Result morphism
         generated_sign CASL _ _ = fun_err "generated_sign"
	 cogenerated_sign CASL _ _ = fun_err "cogenerated_sign"
         -- induced_from_morphism :: id -> EndoMap raw_symbol -> sign -> Result morphism
         induced_from_morphism CASL _ _ = fun_err "induced_from_morphism"
         -- induced_from_to_morphism :: id -> EndoMap raw_symbol -> sign -> sign -> Result morphism 
         induced_from_to_morphism CASL _ _ _ = fun_err "induced_from_to_morphism"
         -- extend_morphism :: Id -> sign -> morphism -> sign -> sign -> Result morphism
         extend_morphism _ _ _ _ _ = fun_err "extend_morphism"

         -- sublogics
         -- sublogic_names :: id -> sublogics -> [String] 
         sublogic_names CASL = Sublogics.sublogics_name
             -- the first name is the principal name
         -- all_sublogics :: id -> [sublogics]
         all_sublogics CASL = fun_err "all_sublogics"

         -- is_in_basic_spec :: id -> sublogics -> basic_spec -> Bool
         is_in_basic_spec CASL = Sublogics.in_basic_spec
         -- is_in_sentence :: id -> sublogics -> sentence -> Bool
         is_in_sentence CASL = Sublogics.in_sentence
         -- is_in_symb_items_list :: id -> sublogics -> symb_items_list -> Bool
         is_in_symb_items_list CASL = Sublogics.in_symb_items_list
         {- is_in_symb_map_items_list :: 
	    id -> sublogics -> symb_map_items_list -> Bool -}
         is_in_symb_map_items_list CASL = Sublogics.in_symb_map_items_list
         -- is_in_sign :: id -> sublogics -> sign -> Bool
         is_in_sign CASL = Sublogics.in_sign
         -- is_in_morphism :: id -> sublogics -> morphism -> Bool
         is_in_morphism CASL _ _ = fun_err "is_in_morphism"
         -- is_in_symbol :: id -> sublogics -> symbol -> Bool
         is_in_symbol CASL = Sublogics.in_symbol

         -- min_sublogic_basic_spec :: id -> basic_spec -> sublogics
         min_sublogic_basic_spec CASL = Sublogics.sl_basic_spec
         -- min_sublogic_sentence :: id -> sentence -> sublogics
         min_sublogic_sentence CASL = Sublogics.sl_sentence
         -- min_sublogic_symb_items_list :: id -> symb_items_list -> sublogics
         min_sublogic_symb_items_list CASL = Sublogics.sl_symb_items_list
         -- min_sublogic_symb_map_items_list :: id -> symb_map_items_list -> sublogics
         min_sublogic_symb_map_items_list CASL = Sublogics.sl_symb_map_items_list
         -- min_sublogic_sign :: id -> sign -> sublogics
         min_sublogic_sign CASL = Sublogics.sl_sign
         -- min_sublogic_morphism :: id -> morphism -> sublogics
         min_sublogic_morphism CASL _ = fun_err "min_sublogic_morphism"
         -- min_sublogic_symbol :: id -> symbol -> sublogics
         min_sublogic_symbol CASL = Sublogics.sl_symbol

         -- proj_sublogic_basic_spec :: id -> sublogics -> basic_spec -> basic_spec
         proj_sublogic_basic_spec CASL _ _ = fun_err "proj_sublogic_basic_spec"
         {- proj_sublogic_symb_items_list :: 
	    id -> sublogics -> symb_items_list -> Maybe symb_items_list -}
         proj_sublogic_symb_items_list CASL _ _ = 
	     fun_err "proj_sublogic_symb_items_list"
         {- proj_sublogic_symb_map_items_list :: id -> 
	    sublogics -> symb_map_items_list -> Maybe symb_map_items_list -}
         proj_sublogic_symb_map_items_list CASL _ _ = 
	     fun_err "proj_sublogic_symb_map_items_list"
-}         -- proj_sublogic_sign :: id -> sublogics -> sign -> sign 
         proj_sublogic_sign CASL _ _ = fun_err "proj_sublogic_sign"
         -- proj_sublogic_morphism :: id -> sublogics -> morphism -> morphism
         proj_sublogic_morphism CASL _ _ = fun_err "proj_sublogic_morphism"
         -- proj_sublogic_epsilon :: id -> sublogics -> sign -> morphism
         proj_sublogic_epsilon CASL _ _ = fun_err "proj_sublogic_epsilon"
         -- proj_sublogic_symbol :: id -> sublogics -> symbol -> Maybe symbol
         proj_sublogic_symbol CASL _ _ = fun_err "proj_sublogic_symbol"

         -- provers
         -- provers :: [Prover sentence symbol]
         provers = fun_err "provers"
         -- cons_checkers :: [Cons_checker (TheoryMorphism sign sentence morphism)] 
         cons_checkers = fun_err "cons_checkers"


-- Simple logic representations (possibly also morphisms via adjointness)
{-

data (Logic id1 sublogics1
        basic_spec1 sentence1 symb_items_list1 symb_map_items_list1
        local_env1 sign1 morphism1 symbol1 raw_symbol1,
      Logic id2 sublogics2
        basic_spec2 sentence2 symb_items_list2 symb_map_items_list2 
        local_env2 sign2 morphism2 symbol2 raw_symbol2) =>
  LogicRepr id1 sublogics1 basic_spec1 sentence1 symb_items_list1 symb_map_items_list1
                local_env1 sign1 morphism1 symbol1 raw_symbol1
            id2 sublogics2 basic_spec2 sentence2 symb_items_list2 symb_map_items_list2
                local_env2 sign2 morphism2 symbol2 raw_symbol2
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
-}

---- helpers ---------------------------------
fun_err fname = 
    error ("*** Function \"" ++ fname ++ "\" is not yet implemented!")

----------------------------------------------