
{- HetCATS/AS_Architecture.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002

   These data structures describe the abstract syntax tree for heterogenous 
   architectural specifications in HetCASL.

   todo:
     - ATermConversion SML-CATS has now his own module 
       (s. HetCATS/aterm_conv/)
     - LaTeX Pretty Printing
-}

module AS_Architecture where

import Id
import AS_Annotation

import AS_Structured
import Grothendieck

{-! global : UpPos !-}

data ARCH_SPEC_DEFN = Arch_spec_defn ARCH_SPEC_NAME (Annoted ARCH_SPEC) [Pos]
		      -- pos: "arch","spec","=",opt "end"
		      deriving (Show,Eq)

data ARCH_SPEC = Basic_arch_spec [Annoted UNIT_DECL_DEFN]
		                 (Annoted UNIT_EXPRESSION) [Pos]
	         -- pos: "unit","result"
	       | Arch_spec_name ARCH_SPEC_NAME
	       | Group_arch_spec (Annoted ARCH_SPEC) [Pos]
		 -- pos: "{","}"
		 deriving (Show,Eq)

data UNIT_DECL_DEFN = Unit_decl UNIT_NAME UNIT_SPEC [Annoted UNIT_TERM] [Pos]
		      -- pos: ":",opt ("given"; Annoted holds pos of commas)
		    | Unit_defn UNIT_NAME UNIT_EXPRESSION [Pos]
		      -- pos: "="
		      deriving (Show,Eq)

data UNIT_SPEC_DEFN = Unit_spec_defn SPEC_NAME UNIT_SPEC [Pos]
		      -- pos: "unit","spec","=", opt "end"
		      deriving (Show,Eq)

data UNIT_SPEC = Unit_type [Annoted SPEC] (Annoted SPEC) [Pos]
	         -- pos: opt "*"s , "->"
	       | Spec_name SPEC_NAME
	       | Arch_unit_spec (Annoted ARCH_SPEC) [Pos] 
		 -- pos: "arch","spec"
		 -- The ARCH_SPEC has to be surrounded with braces and
		 -- after the opening brace is a [Annotation] allowed
	       | Closed_unit_spec UNIT_SPEC [Pos]
		 -- pos: "closed"
		 deriving (Show,Eq)

data UNIT_EXPRESSION = Unit_expression [UNIT_BINDING] (Annoted UNIT_TERM) [Pos]
		       -- pos: opt "lambda",semi colons, "."
		       deriving (Show,Eq)

data UNIT_BINDING = Unit_binding UNIT_NAME UNIT_SPEC [Pos]
		    -- pos: ":"
		    deriving (Show,Eq) 

data UNIT_TERM = Unit_reduction (Annoted UNIT_TERM) RESTRICTION
	       | Unit_translation (Annoted UNIT_TERM) RENAMING 
	       | Amalgamation [Annoted UNIT_TERM] [Pos]
		 -- pos: "and"s
	       | Local_unit [Annoted UNIT_DECL_DEFN] (Annoted UNIT_TERM) [Pos] 
		 -- pos: "local", "within"
	       | Unit_appl UNIT_NAME [FIT_ARG_UNIT] [Pos]
		 -- pos: many of "[","]"
	       | Group_unit_term (Annoted UNIT_TERM) [Pos]
		 -- pos: "{","}"
		 deriving (Show,Eq)

data FIT_ARG_UNIT = Fit_arg_unit (Annoted UNIT_TERM) 
		                 G_symb_map_items_list [Pos] 
		    -- pos: opt "fit"
		    deriving (Show,Eq)

type ARCH_SPEC_NAME = SIMPLE_ID
type UNIT_NAME = SIMPLE_ID