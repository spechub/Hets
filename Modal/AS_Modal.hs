{- HetCATS/Modal/AS_Modal.hs
   $Id
   Author: Wiebke Herding
   Year:    2003

   Example spec:

   spec sp = 
   props p,q,r

   axioms
   . p/\r => q
-}

module Modal.AS_Modal where

import Common.Id
import Common.AS_Annotation

data BASIC_SPEC = Basic_spec [Annoted BASIC_ITEMS]
		deriving (Show,Eq)

data BASIC_ITEMS = Sig_items SIG_ITEMS
		 | Axiom_items [Annoted FORMULA] [Pos]
		   -- pos: dots
		   deriving (Show, Eq)

data SIG_ITEMS = Prop_items [Annoted PROP_ITEM] [Pos]
	       deriving (Show,Eq)

data PROP_ITEM = Prop_decl [PROP] [Pos]
  	       -- pos: commas
	       deriving (Show,Eq)

data FORMULA = Conjunction [FORMULA] [Pos]
	       -- pos: "/\"s
	     | Disjunction [FORMULA] [Pos]
	       -- pos: "\/"s
	     | Implication FORMULA FORMULA [Pos]
	       -- pos: "=>" 
	     | Equivalence FORMULA FORMULA [Pos]
	       -- pos: "<=>"
	     | Negation FORMULA [Pos]
	       -- pos: not
	     | Box FORMULA [Pos]
	       -- pos: "[]"	    
	     | Diamond FORMULA [Pos]
               -- pos: "<>"
	     | Proposition PROP
	       deriving (Show,Eq)

type PROP = Id

type SYMB_ITEMS = Id

type SYMB_MAP_ITEMS = Id
