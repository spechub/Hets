
{- HetCATS/AS_Architecture.hs
   $Id$
   Klaus Luettich

   These data structures describe the abstract syntax tree for heterogenous 
   architectural specifications in HetCASL.

   todo:
-}

module AS_Architecture where
import AS_Structured
import Grothendieck
import Id

data ARCH_SPEC_DEFN = Arch_spec_defn ARCH_SPEC_NAME (Annoted ARCH_SPEC) [Pos]
		      deriving (Show,Eq)

data ARCH_SPEC = Basic_arch_spec [UNIT_DECL_DEFN] UNIT_EXPRESSION [Pos]
	       | Arch_spec_name ARCH_SPEC_NAME [Pos]
		 deriving (Show,Eq)

data UNIT_DECL_DEFN = Unit_decl UNIT_NAME UNIT_SPEC UNIT_IMPORTED [Pos]
		    | Unit_defn UNIT_NAME UNIT_EXPRESSION [Pos]
		      deriving (Show,Eq)

data UNIT_IMPORTED = Unit_imported [UNIT_TERM] [Pos]
		     deriving (Show,Eq)

data UNIT_SPEC_DEFN = Unit_spec_defn SPEC_NAME UNIT_SPEC [Pos]
		      deriving (Show,Eq)

data UNIT_SPEC = Unit_type [SPEC] SPEC [Pos]
	       | Spec_name SPEC_NAME [Pos]
	       | Arch_unit_spec ARCH_SPEC [Pos]
	       | Closed_unit_spec UNIT_SPEC [Pos]
		 deriving (Show,Eq)

data UNIT_EXPRESSION = Unit_expression [UNIT_BINDING] UNIT_TERM [Pos]
		       deriving (Show,Eq)

data UNIT_BINDING = Unit_binding UNIT_NAME UNIT_SPEC [Pos]
		    deriving (Show,Eq) 

data UNIT_TERM = Unit_reduction UNIT_TERM RESTRICTION [Pos]
	       | Unit_translation UNIT_TERM RENAMING [Pos]
	       | Amalgamation [UNIT_TERM] [Pos]
	       | Local_unit [UNIT_DECL_DEFN] UNIT_TERM [Pos] 
	       | Unit_appl UNIT_NAME [FIT_ARG_UNIT] [Pos]
		 deriving (Show,Eq)

data FIT_ARG_UNIT = Fit_arg_unit UNIT_TERM G_symb_map_items_list [Pos] 
		    deriving (Show,Eq)

type ARCH_SPEC_NAME = SIMPLE_ID
type UNIT_NAME = SIMPLE_ID