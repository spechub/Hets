{- |
Module      :  $Header$
Description :  Abstract syntax for common logic
Copyright   :  Karl Luc, Uni Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.tx

Maintainer  :  kluc@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Definition of abstract syntax for common logic
-}

{-
  Ref.
  ISO/IEC IS 24707:2007(E)
-}

module CommonLogic.AS_CommonLogic where

import Common.Id as Id
import Common.Doc
import Common.DocUtils
import Common.Keywords

data TEXT = Text [PHRASE] Id.Range
            deriving (Show, Ord, Eq)

data PHRASE = Module MODULE Id.Range
            | Sentence SENTENCE Id.Range
            | Importation IMPORTATION Id.Range
            | Comment_Text TEXT COMMENT Id.Range
              deriving (Show, Ord, Eq)

data COMMENT = Comment String Id.Range
               deriving (Show, Ord, Eq)

data MODULE = Mod NAME [NAME] TEXT Id.Range
              -- Name, ExclusionSet, BodyText
              deriving (Show, Ord, Eq)

data IMPORTATION = Imp_name NAME Id.Range
                   deriving (Show, Ord, Eq)

data SENTENCE = Quant_sent QUANT_SENT Id.Range
              | Bool_sent BOOL_SENT Id.Range
              | Atom_sent ATOM Id.Range
              | Comment_sent SENTENCE COMMENT Id.Range
              | Irregular_sent Id.Range
                deriving (Show, Ord, Eq)

data QUANT_SENT = Universal BINDING_SEQ SENTENCE Id.Range
                | Existential BINDING_SEQ SENTENCE Id.Range
                  deriving (Show, Ord, Eq)

data BINDING_SEQ = Binding [NAME] [SEQ_MARK] Id.Range
                   -- a finite nonrepeating sequence of names and sequence markers
                   deriving (Show, Ord, Eq)

data BOOL_SENT = Conjunction [SENTENCE] Id.Range
               | Disjunction [SENTENCE] Id.Range
               | Negation SENTENCE Id.Range
               | Implication SENTENCE SENTENCE Id.Range
               | Biconditional SENTENCE SENTENCE Id.Range
                 deriving (Show, Ord, Eq)

data ATOM = Equation TERM TERM Id.Range
          | Atom TERM TERM_SEQ Id.Range
            deriving (Show, Ord, Eq)

data TERM = Name NAME Id.Range
          | Funct_term TERM TERM_SEQ Id.Range
          | Comment_term TERM COMMENT Id.Range
            deriving (Show, Ord, Eq)

data TERM_SEQ = Term_seq [TERM] Id.Range
              | Seq_marks [SEQ_MARK] Id.Range
                deriving (Show, Ord, Eq)

type NAME = String

type SEQ_MARK = String

--

-- pretty printing, dummy
instance Pretty SENTENCE where
   pretty = printSentence

printSentence :: SENTENCE -> Doc
printSentence s = case s of
    Quant_sent _ _  -> text falseS
    Bool_sent _ _ -> text falseS
    Atom_sent _ _ -> text falseS
    Comment_sent _ _ _ -> text falseS
    Irregular_sent _ -> text falseS
