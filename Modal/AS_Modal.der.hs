{-
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Wiebke Herding, C. Maeder, Uni Bremen 2004
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

  Abstract syntax for modal logic extension of CASL
  Only the added syntax is specified
-}

module Modal.AS_Modal where

import Common.Id
import Common.AS_Annotation 
import CASL.AS_Basic_CASL
import CASL.ATC_CASL

-- DrIFT command
{-! global: UpPos !-}

type M_BASIC_SPEC = BASIC_SPEC M_BASIC_ITEM M_SIG_ITEM M_FORMULA

data M_BASIC_ITEM = Simple_mod_decl [Annoted SIMPLE_ID] [Pos]
		  | Term_mod_decl [Annoted SORT] [Pos]
		    deriving (Eq, Show)

data RIGOR = Rigid | Flexible deriving (Eq, Show)

data M_SIG_ITEM =
	  Rigid_op_items RIGOR [Annoted (OP_ITEM M_FORMULA)] [Pos]
		 -- pos: op, semi colons
	| Rigid_pred_items RIGOR [Annoted (PRED_ITEM M_FORMULA)] [Pos]
		 -- pos: pred, semi colons
             deriving (Eq, Show)

-- type ModalFORMULA = FORMULA M_FORMULA

data MODALITY = Simple_mod SIMPLE_ID | Term_mod (TERM M_FORMULA)
             deriving (Eq, Ord, Show)

data M_FORMULA = 
	       Box MODALITY (FORMULA M_FORMULA) [Pos]
               -- The identifier and the term specify the kind of the modality
	       -- pos: "[]"	    
	     | Diamond MODALITY (FORMULA M_FORMULA) [Pos]
               -- The identifier and the term specify the kind of the modality
               -- pos: "<>"
             deriving (Eq, Ord, Show)

modalityS, modalitiesS, flexibleS, rigidS, termS, emptyS :: String 
modalityS = "modality"
modalitiesS = init modalityS ++ "ies"
flexibleS = "flexible"
rigidS = "rigid"
termS = "term"
emptyS = "empty" 

modal_reserved_words :: [String]
modal_reserved_words = termS:rigidS:flexibleS:modalityS:[modalitiesS]
