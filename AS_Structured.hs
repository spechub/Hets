-- needs ghc -fglasgow-exts -package lang

{- HetCATS/AS_Structured.hs
   $Id$
   Klaus Luettich

   These data structures describe the abstract syntax tree for heterogenous 
   structured specifications in HetCASL.

   todo:
   Deriving Show and Eq is not so easy with stuff from the Grothendieck logic
-}

module AS_Structured where
import Id
import Grothendieck
import Logic

data SPEC = Basic_spec G_basic_spec 
	  | Translation(SPEC,RENAMING)
	  | Reduction(SPEC,RESTRICTION)
	  | Union [SPEC]
	  | Extension [SPEC]
	  | Free_spec SPEC
	  | Local_spec(SPEC,SPEC)
	  | Closed_spec(SPEC)
          | Group SPEC
          | Spec_inst(SPEC_NAME,[FIT_ARG])
	    deriving (Show,Eq)


data RENAMING = Renaming G_symb_map_items_list
		deriving (Show,Eq)

data RESTRICTION = Hidden G_symb_items_list
		 | Revealed G_symb_map_items_list
		   deriving (Show,Eq)

data SPEC_DEFN = Spec_defn(SPEC_NAME,GENERICITY,SPEC)
		 deriving (Show,Eq)

data GENERICITY = Genericity(PARAMS,IMPORTED)
		  deriving (Show,Eq)

data PARAMS = Params [SPEC]
	      deriving (Show,Eq)

data IMPORTED = Imported [SPEC]
		deriving (Show,Eq)

data FIT_ARG = Fit_spec(SPEC,G_symb_map_items_list)
	     | Fit_view(VIEW_NAME,[FIT_ARG])
	       deriving (Show,Eq)

data VIEW_DEFN = View_defn(VIEW_NAME,GENERICITY,VIEW_TYPE,
			   G_symb_map_items_list)
		  deriving (Show,Eq)

data VIEW_TYPE = View_type(SPEC,SPEC)
		 deriving (Show,Eq)

type SPEC_NAME = SIMPLE_ID
type VIEW_NAME = SIMPLE_ID
