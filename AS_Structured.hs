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
import Grothendieck
import Logic

data SPEC = Basic_spec G_basic_spec 
	  | Translation SPEC RENAMING 
	  | Reduction SPEC RESTRICTION 
	  | Union [SPEC] [Pos]
	  | Extension [SPEC] [Pos]
	  | Free_spec SPEC [Pos]
	  | Local_spec SPEC SPEC [Pos]
	  | Closed_spec SPEC [Pos]
          | Group SPEC [Pos]
          | Spec_inst SPEC_NAME [FIT_ARG] 
	    deriving (Show,Eq)


data RENAMING = Renaming G_symb_map_items_list [Pos]
		deriving (Show,Eq)

data RESTRICTION = Hidden G_symb_items_list [Pos]
		 | Revealed G_symb_map_items_list [Pos]
		   deriving (Show,Eq)

data SPEC_DEFN = Spec_defn SPEC_NAME GENERICITY SPEC [Pos]
               -- 
		 deriving (Show,Eq)

data GENERICITY = Genericity PARAMS IMPORTED [Pos]
		  deriving (Show,Eq)

data PARAMS = Params [SPEC] [Pos]
	      deriving (Show,Eq)

data IMPORTED = Imported [SPEC] [Pos]
		deriving (Show,Eq)

data FIT_ARG = Fit_spec SPEC G_symb_map_items_list [Pos] 
	     | Fit_view VIEW_NAME [FIT_ARG] [Pos]
	       deriving (Show,Eq)

data VIEW_DEFN = View_defn VIEW_NAME GENERICITY VIEW_TYPE 
			   G_symb_map_items_list [Pos]
		  deriving (Show,Eq)

data VIEW_TYPE = View_type SPEC SPEC [Pos]
		 deriving (Show,Eq)

type SPEC_NAME = SIMPLE_ID
type VIEW_NAME = SIMPLE_ID

