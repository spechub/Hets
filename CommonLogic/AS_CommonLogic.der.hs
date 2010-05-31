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
import qualified Common.AS_Annotation as AS_Anno

-- DrIFT command
{-! global: GetRange !-}

newtype BASIC_SPEC = Basic_spec [AS_Anno.Annoted (BASIC_ITEMS)]
                      deriving Show

data BASIC_ITEMS =
    Axiom_items [AS_Anno.Annoted (SENTENCE)]
    deriving Show

instance Pretty BASIC_SPEC where
    pretty = printBasicSpec
instance Pretty BASIC_ITEMS where
    pretty = printBasicItems

printBasicSpec :: BASIC_SPEC -> Doc
printBasicSpec (Basic_spec xs) = vcat $ map pretty xs

printBasicItems :: BASIC_ITEMS -> Doc
printBasicItems (Axiom_items xs) = vcat $ map pretty xs

-- Common Logic Syntax
data TEXT = Text [PHRASE] Id.Range
          | Named_text String TEXT Id.Range
            deriving (Show, Ord, Eq)

data PHRASE = Module MODULE
            | Sentence SENTENCE
            | Importation IMPORTATION
            | Comment_text COMMENT TEXT Id.Range
              deriving (Show, Ord, Eq)

data COMMENT = Comment String Id.Range
               deriving (Show, Ord, Eq)

data MODULE = Mod NAME TEXT Id.Range
            | Mod_ex NAME [NAME] TEXT Id.Range
              deriving (Show, Ord, Eq)

data IMPORTATION = Imp_name NAME
                   deriving (Show, Ord, Eq)

data SENTENCE = Quant_sent QUANT_SENT Id.Range
              | Bool_sent BOOL_SENT Id.Range
              | Atom_sent ATOM Id.Range
              | Comment_sent COMMENT SENTENCE Id.Range
              | Irregular_sent SENTENCE Id.Range
                deriving (Show, Ord, Eq)

data QUANT_SENT = Universal [NAME_OR_SEQMARK] SENTENCE
                | Existential [NAME_OR_SEQMARK] SENTENCE
                  --
                  deriving (Show, Ord, Eq)

data BOOL_SENT = Conjunction [SENTENCE]
               | Disjunction [SENTENCE]
               | Negation SENTENCE
               | Implication SENTENCE SENTENCE
               | Biconditional SENTENCE SENTENCE
                 deriving (Show, Ord, Eq)

data ATOM = Equation TERM TERM
          | Atom TERM [TERM_SEQ]
            deriving (Show, Ord, Eq)

data TERM = Name_term NAME
          | Funct_term TERM [TERM_SEQ] Id.Range
          | Comment_term TERM COMMENT Id.Range
            deriving (Show, Ord, Eq)
{-
data TERM_SEQ = Term_seq [TERM] Id.Range
              | Seq_marks [SEQ_MARK] Id.Range
                deriving (Show, Ord, Eq)

data TERM_SEQ = Term_seq [TERM_OR_SEQMARK] Id.Range
                deriving (Show, Ord, Eq)
-}

data TERM_SEQ = Term_seq TERM
              | Seq_marks SEQ_MARK
                deriving (Show, Ord, Eq)


type NAME = Id.Token
type SEQ_MARK = Id.Token

-- binding seq
data NAME_OR_SEQMARK = Name NAME
                     | SeqMark SEQ_MARK
                       deriving (Show, Eq, Ord)

data SYMB_MAP_ITEMS = Symb_map_items [NAME_OR_SEQMARK] Id.Range
                      deriving (Show, Eq)

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
instance Pretty COMMENT where
   pretty = printComment
instance Pretty NAME_OR_SEQMARK where
   pretty = printNameOrSeqMark

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
   Atom t ts -> parens $ pretty t <+> (sep $ map pretty ts)

printTerm :: TERM -> Doc
printTerm s = case s of
   Name_term a -> pretty a
   Funct_term t ts _ -> parens $ pretty t <+> (fsep $ map pretty ts)
   Comment_term x y _ -> pretty x <+> pretty y

printTermSeq :: TERM_SEQ -> Doc
printTermSeq s = case s of
  Term_seq t -> pretty t
  Seq_marks m -> pretty m

-- Binding Seq
printNameOrSeqMark :: NAME_OR_SEQMARK -> Doc
printNameOrSeqMark s = case s of
  Name x -> pretty x
  SeqMark x -> pretty x
  -- Alt x y -> pretty x <+> pretty y

instance Pretty TEXT where
   pretty = printText
instance Pretty PHRASE where
   pretty = printPhrase
instance Pretty MODULE where
   pretty = printModule
instance Pretty IMPORTATION where
   pretty = printImportation

printText :: TEXT -> Doc
printText s = case s of
  Text x _ -> fsep $ map pretty x
  Named_text x y _ -> text x <+> pretty y

printPhrase :: PHRASE -> Doc
printPhrase s = case s of
  Module x -> pretty x
  Sentence x -> pretty x
  Importation x -> pretty x
  Comment_text x y _ -> pretty x <+> pretty y

printModule :: MODULE -> Doc
printModule (Mod x z _) = pretty x <+> pretty z
printModule (Mod_ex x y z _)  = pretty x <+> fsep (map pretty y) <+> pretty z

printImportation :: IMPORTATION -> Doc
printImportation (Imp_name x) = pretty x

-- keywords, reservednames in CLIF
seqmarkS :: String
seqmarkS = "..."

(...) :: String
(...) = "..."

orS :: String
orS = "or"

iffS :: String
iffS = "iff"
