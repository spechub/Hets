{- |
Module      :  $Header$
Description :  Abstract syntax for common logic
Copyright   :
License     :

Maintainer  :  kluc
Stability   :  provisional
Portability :

Definition of abstract syntax for common logic
-}

{-
  Ref.
  ISO/IEC IS 24707:2007(E)
-}

module CommonLogic.AS_CommonLogic where

-- import Common.Id as Id

data TEXT = Text [PHRASE]
     	    deriving Show

data PHRASE = Module MODULE
     	    | Sentence SENTENCE
	    | Importation IMPORTATION
	    | Comment_Text TEXT COMMENT
     	      deriving Show

data COMMENT = Comment String
     	       -- comment: piece of data, undefined
     	       deriving Show

data MODULE = Mod NAME [NAME] TEXT
     	      -- Name, ExclusionSet, BodyText
     	      deriving Show

data IMPORTATION = Imp_name NAME
     		   deriving Show

data SENTENCE = Quant_sent QUANT_SENT
     	      | Bool_sent BOOL_SENT
	      | Atom_sent ATOM
	      | Comment_sent SENTENCE COMMENT
	      | Irregular_sent
	      	deriving Show

data QUANT_SENT = Universal BINDING_SEQ SENTENCE
     		| Existential BINDING_SEQ SENTENCE
		  deriving Show

data BINDING_SEQ = Binding [NAME] [SEQ_MARK]
		   -- a finite nonrepeating sequence of names and sequence markers
     		   deriving Show

data BOOL_SENT = Conjunction [SENTENCE]
     	       | Disjunction [SENTENCE]
	       | Negation SENTENCE
	       | Implication SENTENCE SENTENCE
	       | Biconditional SENTENCE SENTENCE
	       	 deriving Show

data ATOM = Equation TERM TERM
     	  | Atom TERM TERM_SEQ
	    deriving Show

data TERM = Name NAME
	  | Funct_term TERM TERM_SEQ
	  | Comment_term TERM COMMENT
	    deriving Show

data TERM_SEQ = Term_seq [TERM]
     	      | Seq_marks [SEQ_MARK]
	      	deriving Show

type NAME = String

type SEQ_MARK = String
