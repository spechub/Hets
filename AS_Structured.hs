-- needs ghc -fglasgow-exts

{- HetCATS/AS_Structured.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002

   These data structures describe the abstract syntax tree for heterogenous 
   structured specifications in HetCASL.

   todo:
   Deriving Show and Eq is not so easy with stuff from the Grothendieck logic
-}

{-! global: ATermConvertible !-}

module AS_Structured where

import Id
import AS_Annotation

import Grothendieck
import Logic

data SPEC = Basic_spec G_basic_spec 
	  | Translation (Annoted SPEC) RENAMING 
	  | Reduction (Annoted SPEC) RESTRICTION 
	  | Union [(Annoted SPEC)] [Pos]
	    -- pos: "and"s
	  | Extension [(Annoted SPEC)] [Pos]
	    -- pos: "then"s
	  | Free_spec (Annoted SPEC) [Pos]
	    -- pos: "free"
	  | Local_spec (Annoted SPEC) (Annoted SPEC) [Pos]
	    -- pos: "local", "within"
	  | Closed_spec (Annoted SPEC) [Pos]
	    -- pos: "closed"
          | Group (Annoted SPEC) [Pos]
	    -- pos: "{","}"
          | Spec_inst SPEC_NAME [Annoted FIT_ARG]
	    -- pos: many of "[","]"; one balanced pair per FIT_ARG
	    deriving (Show,Eq)


data RENAMING = Renaming G_symb_map_items_list [Pos]
	        -- pos: "with"; comma pos is stored inside the list
		deriving (Show,Eq)

data RESTRICTION = Hidden G_symb_items_list [Pos]
		   -- pos: "hide"; comma pos is stored inside the list
		 | Revealed G_symb_map_items_list [Pos]
		   -- pos: "reveal"; comma pos is stored inside the list
		   deriving (Show,Eq)

data SPEC_DEFN = Spec_defn SPEC_NAME GENERICITY (Annoted SPEC) [Pos]
	         -- pos: "spec","=",opt "end"
		 deriving (Show,Eq)

data GENERICITY = Genericity PARAMS IMPORTED [Pos]
		  -- pos: many of "[","]" opt ("given", commas) 
		  deriving (Show,Eq)

data PARAMS = Params [Annoted SPEC]
	      deriving (Show,Eq)

data IMPORTED = Imported [Annoted SPEC]
		deriving (Show,Eq)

data FIT_ARG = Fit_spec (Annoted SPEC) G_symb_map_items_list [Pos]
	       -- pos: opt "fit"
	     | Fit_view VIEW_NAME [Annoted FIT_ARG] [Pos] [Annotation]
	       -- The list of Annotations is written before the keyword 'view'
	       -- pos: "view", opt many of "[","]"
	       deriving (Show,Eq)

data VIEW_DEFN = View_defn VIEW_NAME GENERICITY VIEW_TYPE
			   G_symb_map_items_list [Pos]
	         -- pos: "view",":",opt "=", opt "end" 
		  deriving (Show,Eq)

data VIEW_TYPE = View_type (Annoted SPEC) (Annoted SPEC) [Pos]
	         -- pos: "to"
		 deriving (Show,Eq)

type SPEC_NAME = SIMPLE_ID
type VIEW_NAME = SIMPLE_ID

