{-
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2004
Licence     :  All rights reserved.

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  portable

  Abstract syntax for CoCASL, the coalgebraic extension of CASL
  Only the added syntax is specified
-}

module Modal.AS_CoCASL where

import Common.Id
import Common.AS_Annotation 
import CASL.AS_Basic_CASL
import CASL.ATC_CASL

-- DrIFT command
{-! global: UpPos !-}

type C_BASIC_SPEC = BASIC_SPEC C_BASIC_ITEM C_SIG_ITEM C_FORMULA

type AnModFORM = Annoted (FORMULA C_FORMULA)

data C_BASIC_ITEM = CoFree_datatype [Annoted CODATATYPE_DECL] [Pos]
		   -- pos: free, type, semi colons
	 	  | CoSort_gen [Annoted (SIG_ITEMS C_SIG_ITEM C_FORMULA)] [Pos] 
		   -- pos: generated, opt. braces 

Simple_mod_decl [Annoted SIMPLE_ID] [AnModFORM] [Pos]
		  | Term_mod_decl [Annoted SORT] [AnModFORM] [Pos]
		    deriving (Eq, Show)

data C_SIG_ITEM = CoDatatype_items [Annoted CODATATYPE_DECL] [Pos]
		 -- type, semi colons
             deriving (Eq, Show)

data CODATATYPE_DECL = CoDatatype_decl SORT [Annoted COALTERNATIVE] [Pos] 
		     -- pos: "::=", "|"s
		     deriving (Show,Eq)

data COALTERNATIVE = CoTotal_construct (Maybe OP_NAME) [COCOMPONENTS] [Pos]
		   -- pos: "(", semi colons, ")"
		 | CoPartial_construct (Maybe OP_NAME) [COCOMPONENTS] [Pos]
		   -- pos: "(", semi colons, ")", "?"
		 | CoSubsorts [SORT] [Pos]
		   -- pos: sort, commas
		   deriving (Show,Eq)

data COCOMPONENTS = CoTotal_select [OP_NAME] SORT [Pos]
                  -- pos: commas, colon
		| CoPartial_select [OP_NAME] SORT [Pos] 
		  -- pos: commas, ":?"

data MODALITY = Simple_mod SIMPLE_ID | Term_mod (TERM C_FORMULA)
             deriving (Eq, Ord, Show)

data C_FORMULA = 
	       Box MODALITY (FORMULA C_FORMULA) [Pos]
               -- The identifier and the term specify the kind of the modality
	       -- pos: "[]"	    
	     | Diamond MODALITY (FORMULA C_FORMULA) [Pos]
               -- The identifier and the term specify the kind of the modality
               -- pos: "<>"
             deriving (Eq, Ord, Show)

cotypeS, cotypesS, cogeneratedS, diamondS, greaterS 
    :: String 
cotypeS = "cotype"
cotypesS = "cotypes"
cogeneratedS = "cogenerated"
diamondS = "<>"
greaterS = ">"

cocasl_reserved_words :: [String]
cocasl_reserved_words = [cotypeS, cotypesS, cogeneratedS, diamondS, greaterS]
