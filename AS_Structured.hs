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
	  | Translation (Annoted SPEC) RENAMING 
	  | Reduction (Annoted SPEC) RESTRICTION 
	  | Union [(Annoted SPEC)] [Pos]
	  | Extension [(Annoted SPEC)] [Pos]
	  | Free_spec (Annoted SPEC) [Pos]
	  | Local_spec (Annoted SPEC) (Annoted SPEC) [Pos]
	  | Closed_spec (Annoted SPEC) [Pos]
          | Group (Annoted SPEC) [Pos]
          | Spec_inst SPEC_NAME [FIT_ARG] 
	    deriving (Show,Eq)


data RENAMING = Renaming G_symb_map_items_list [Pos]
		deriving (Show,Eq)

data RESTRICTION = Hidden G_symb_items_list [Pos]
		 | Revealed G_symb_map_items_list [Pos]
		   deriving (Show,Eq)

data SPEC_DEFN = Spec_defn SPEC_NAME GENERICITY (Annoted SPEC) [Pos]
		 deriving (Show,Eq)

data GENERICITY = Genericity PARAMS IMPORTED [Pos]
		  deriving (Show,Eq)

data PARAMS = Params [Annoted SPEC] [Pos]
	      deriving (Show,Eq)

data IMPORTED = Imported [Annoted SPEC] [Pos]
		deriving (Show,Eq)

data FIT_ARG = Fit_spec (Annoted SPEC) G_symb_map_items_list [Pos] 
	     | Fit_view VIEW_NAME [FIT_ARG] [Pos]
	       deriving (Show,Eq)

data VIEW_DEFN = View_defn VIEW_NAME GENERICITY VIEW_TYPE 
			   G_symb_map_items_list [Pos]
		  deriving (Show,Eq)

data VIEW_TYPE = View_type (Annoted SPEC) (Annoted SPEC) [Pos]
		 deriving (Show,Eq)

type SPEC_NAME = SIMPLE_ID
type VIEW_NAME = SIMPLE_ID

