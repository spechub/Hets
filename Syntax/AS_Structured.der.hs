-- needs ghc -fglasgow-exts

{- HetCATS/Syntax/AS_Structured.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002

   These data structures describe the abstract syntax tree for heterogenous 
   structured specifications in HetCASL.

   todo:
     - ATermConversion SML-CATS has now his own module 
       (s. HetCATS/aterm_conv/)
     - LaTeX Pretty Printing
-}

module Syntax.AS_Structured where

-- DrIFT command:
{-! global: UpPos !-}

import Common.Id
import Common.AS_Annotation

import Logic.Grothendieck

data SPEC = Basic_spec G_basic_spec 
	  | Translation (Annoted SPEC) RENAMING 
	  | Reduction (Annoted SPEC) RESTRICTION 
	  | Union [(Annoted SPEC)] [Pos]
	    -- pos: "and"s
	  | Extension [(Annoted SPEC)] [Pos]
	    -- pos: "then"s
	  | Free_spec (Annoted SPEC) [Pos]
	    -- pos: "free"
	  | Cofree_spec (Annoted SPEC) [Pos]
	    -- pos: "cofree"
	  | Local_spec (Annoted SPEC) (Annoted SPEC) [Pos]
	    -- pos: "local", "within"
	  | Closed_spec (Annoted SPEC) [Pos]
	    -- pos: "closed"
          | Group (Annoted SPEC) [Pos]
	    -- pos: "{","}"
          | Spec_inst SPEC_NAME [Annoted FIT_ARG] [Pos]
	    -- pos: many of "[","]"; one balanced pair per FIT_ARG
	  | Qualified_spec Logic_name (Annoted SPEC) [Pos]
	    -- pos: "logic", Logic_name,":"
	    deriving (Show,Eq)


{- Renaming and Hiding can be performend with intermediate Logic
   mappings / Logic projections.

-}
data RENAMING = Renaming [G_mapping] [Pos]
	        -- pos: "with", list of comma pos 
		 deriving (Show,Eq)

data RESTRICTION = Hidden [G_hiding] [Pos]
		   -- pos: "hide", list of comma pos 
		 | Revealed G_symb_map_items_list [Pos]
		   -- pos: "reveal", list of comma pos 
		   deriving (Show,Eq)

data G_mapping = G_symb_map G_symb_map_items_list
	       | G_logic_translation Logic_code
		 deriving (Show,Eq)

data G_hiding = G_symb_list G_symb_items_list
	       | G_logic_projection Logic_code
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
			   [G_mapping] [Pos]
	         -- pos: "view",":",opt "=", opt "end" 
		  deriving (Show,Eq)

data VIEW_TYPE = View_type (Annoted SPEC) (Annoted SPEC) [Pos]
	         -- pos: "to"
		 deriving (Show,Eq)

type SPEC_NAME = SIMPLE_ID
type VIEW_NAME = SIMPLE_ID

data Logic_code = Logic_code (Maybe Token) 
                             (Maybe Logic_name) 
			     (Maybe Logic_name) [Pos]
		 -- pos: "logic",<encoding>,":",<src-logic>,"->",<targ-logic>
                 -- one of <encoding>, <src-logic> or <targ-logic>
                 -- must be given (by Just)
                 -- "logic bla"    => <encoding> only 
                 -- "logic bla ->" => <src-logic> only
                 -- "logic -> bla" => <targ-logic> only
                 -- "logic bla1 -> bla2" => <src-logic> and <targ-logic>
                 -- -- "logic bla1:bla2"    => <encoding> and <src-logic>
                 -- ^ this notation is not very useful and is not maintained
                 -- "logic bla1:bla2 ->" => <encoding> and <src-logic> (!)
                 -- "logic bla1: ->bla2" => <encoding> and <targ-logic>
		  deriving (Show,Eq)

data Logic_name = Logic_name Token (Maybe Token)
		  deriving (Show,Eq)

