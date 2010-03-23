{- |
Module      :  $Header$
Description :  Abstract syntax for common logic
Copyright   :  (c) Karl Luc, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

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
              deriving (Show, Ord, Eq)

data IMPORTATION = Imp_name NAME Id.Range
                   deriving (Show, Ord, Eq)

data SENTENCE = Quant_sent QUANT_SENT Id.Range
              | Bool_sent BOOL_SENT Id.Range
              | Atom_sent ATOM Id.Range
              | Comment_sent SENTENCE COMMENT Id.Range
              | Irregular_sent SENTENCE Id.Range -- opt
                deriving (Show, Ord, Eq)

data QUANT_SENT = Universal [BINDING_SEQ] SENTENCE
                | Existential [BINDING_SEQ] SENTENCE
                  deriving (Show, Ord, Eq)

data BINDING_SEQ = B_name NAME Id.Range
                 | B_seqmark SEQ_MARK Id.Range
                   deriving (Show, Ord, Eq)

data BOOL_SENT = Conjunction [SENTENCE]
               | Disjunction [SENTENCE]
               | Negation SENTENCE
               | Implication SENTENCE SENTENCE
               | Biconditional SENTENCE SENTENCE
                 deriving (Show, Ord, Eq)

data ATOM = Equation TERM TERM
          | Atom TERM TERM_SEQ
            deriving (Show, Ord, Eq)

data TERM = Name NAME Id.Range
          | Funct_term TERM TERM_SEQ Id.Range
          | Comment_term TERM COMMENT Id.Range
            deriving (Show, Ord, Eq)

data TERM_SEQ = Term_seq [TERM] Id.Range
              | Seq_marks [SEQ_MARK] Id.Range
                deriving (Show, Ord, Eq)

type NAME = Id.Token

type SEQ_MARK = Id.Token

{-
newtype NAME = Name Id.Token
               deriving (Show, Eq)

newtype SEQ_MARK = SeqMark Id.Token
                   deriving (Show, Eq)
-}

-- pretty printing using CLIF

instance Pretty SENTENCE where
   pretty = printSentence
instance Pretty BOOL_SENT where
   pretty = printBoolSent
instance Pretty QUANT_SENT where
   pretty = printQuantSent
instance Pretty ATOM where
   pretty = printAtom
instance Pretty TERM where
   pretty = printTerm
instance Pretty TERM_SEQ where
   pretty = printTermSeq
instance Pretty BINDING_SEQ where
   pretty = printBindingSeq
instance Pretty COMMENT where
   pretty = printComment

printSentence :: SENTENCE -> Doc
printSentence s = case s of
    Quant_sent xs _ -> parens $ pretty xs
    Bool_sent xs _ -> parens $ pretty xs
    Atom_sent xs _ -> pretty xs
    Comment_sent x y _ -> parens $ pretty y <+> pretty x
    Irregular_sent xs _ -> parens $ pretty xs

printComment :: COMMENT -> Doc
printComment s = case s of
   Comment x _ -> text x

printQuantSent :: QUANT_SENT -> Doc
printQuantSent s = case s of
   Universal x y -> text forallS <+> parens (sep $ map pretty x)<+> pretty y
   Existential x y -> text existsS <+> parens (sep $ map pretty x) <+> pretty y

printBindingSeq :: BINDING_SEQ -> Doc
printBindingSeq s = case s of
   B_name xs _ -> pretty xs
   B_seqmark xs _ -> text seqmark <> pretty xs

printBoolSent :: BOOL_SENT -> Doc
printBoolSent s = case s of
   Conjunction xs -> text andS <+> (fsep $ map pretty xs)
   Disjunction xs -> text orS <+> (fsep $ map pretty xs)
   Negation xs -> text notS <+> pretty xs
   Implication x y -> text ifS <+> pretty x <+> pretty y
   Biconditional x y -> text iffS <+> pretty x <+> pretty y

printAtom :: ATOM -> Doc
printAtom s = case s of
   Equation a b -> parens $ equals <+> pretty a <+> pretty b
   Atom t ts -> parens $ pretty t <+> pretty ts

printTerm :: TERM -> Doc
printTerm s = case s of
   Name a _ -> pretty a
   Funct_term t ts _ -> parens $ pretty t <+> pretty ts
   Comment_term x y _ -> pretty x <+> pretty y

printTermSeq :: TERM_SEQ -> Doc
printTermSeq s = case s of
  Term_seq t _ -> fsep $ map pretty t
  Seq_marks m _ -> fsep $ map pretty m

-- keywords, reservednames in CLIF

seqmark :: String
seqmark = "..."

(...) :: String
(...) = "..."

orS :: String
orS = "or"

iffS :: String 
iffS = "iff"