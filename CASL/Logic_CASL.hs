
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
data CASL = CASL deriving (Show)
instance Language CASL where  -- default definition is okay

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


-- abstract syntax, parsing (and printing)

instance Syntax CASL BASIC_SPEC 
		SYMB_ITEMS SYMB_MAP_ITEMS
      where 
         parse_basic_spec CASL = Just(basicSpec)
	 parse_symb_items CASL = symbItems
	 parse_symb_map_items CASL = symbMapItems

-- lattices (for sublogics)

instance LatticeWithTop Sublogics.CASL_Sublogics where
    -- meet, join :: l -> l -> l
    meet = Sublogics.sublogics_min
    join = Sublogics.sublogics_max
    -- top :: l
    top = Sublogics.top

-- CASL logic

instance Sentences CASL Sentence LocalEnv Sign String Symbol where
-- missing

instance StaticAnalysis CASL BASIC_SPEC Sentence 
               SYMB_ITEMS SYMB_MAP_ITEMS
               LocalEnv Sign 
               String -- morphism 
               Symbol RawSymbol where
-- missing

instance Logic CASL Sublogics.CASL_Sublogics
               BASIC_SPEC Sentence SYMB_ITEMS SYMB_MAP_ITEMS
               LocalEnv Sign 
               String -- Morphism 
               Symbol RawSymbol where
         sublogic_names CASL = Sublogics.sublogics_name

         is_in_basic_spec CASL = Sublogics.in_basic_spec
         is_in_sentence CASL = Sublogics.in_sentence
         is_in_symb_items CASL = Sublogics.in_symb_items
         is_in_symb_map_items CASL = Sublogics.in_symb_map_items
         is_in_sign CASL = Sublogics.in_sign
--         is_in_morphism CASL = Sublogics.in_morphism
         is_in_symbol CASL = Sublogics.in_symbol

         min_sublogic_basic_spec CASL = Sublogics.sl_basic_spec
         min_sublogic_sentence CASL = Sublogics.sl_sentence
         min_sublogic_symb_items CASL = Sublogics.sl_symb_items
         min_sublogic_symb_map_items CASL = Sublogics.sl_symb_map_items
         min_sublogic_sign CASL = Sublogics.sl_sign
--         min_sublogic_morphism CASL = Sublogics.sl_morphism
         min_sublogic_symbol CASL = Sublogics.sl_symbol

         proj_sublogic_basic_spec CASL = Sublogics.pr_basic_spec
         proj_sublogic_symb_items CASL = Sublogics.pr_symb_items
         proj_sublogic_symb_map_items CASL = Sublogics.pr_symb_map_items
         proj_sublogic_sign CASL = Sublogics.pr_sign
--         proj_sublogic_morphism CASL = Sublogics.pr_morphism
         proj_sublogic_symbol CASL = Sublogics.pr_symbol

---- helpers ---------------------------------
fun_err fname = 
    error ("*** Function \"" ++ fname ++ "\" is not yet implemented!")

----------------------------------------------
