{- |
Module      :  $Header$
Description :  Abstract syntax for common logic
Copyright   :  (c) Karl Luc, DFKI Bremen 2010
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
              deriving (Show, Ord, Eq)

data IMPORTATION = Imp_name NAME Id.Range
                   deriving (Show, Ord, Eq)

data SENTENCE = Quant_sent QUANT_SENT Id.Range
              | Bool_sent BOOL_SENT Id.Range
              | Atom_sent ATOM Id.Range
              | Comment_sent SENTENCE COMMENT Id.Range
              | Irregular_sent Id.Range
                deriving (Show, Ord, Eq)

data QUANT_SENT = Universal [BINDING_SEQ] SENTENCE Id.Range
                | Existential [BINDING_SEQ] SENTENCE Id.Range
                  deriving (Show, Ord, Eq)

data BINDING_SEQ = B_name NAME Id.Range
                 | B_seqmark SEQ_MARK Id.Range
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

printSentence :: SENTENCE -> Doc
printSentence s = case s of
    Quant_sent b _  -> br $ printQuantSent b
    Bool_sent b _ -> br $ printBoolSent b
    Atom_sent b _ -> printAtom b
    Comment_sent _ _ _ -> text falseS -- opt.
    Irregular_sent _ -> text falseS   -- opt.

printQuantSent :: QUANT_SENT -> Doc
printQuantSent s = case s of
   Universal a b _ -> text forallS <+> br (sep $ map printBindingSeq a)<+> printSentence b
   Existential a b _ -> text existsS <+> br (sep $ map printBindingSeq a) <+> printSentence b

printBindingSeq :: BINDING_SEQ -> Doc
printBindingSeq s = case s of
   B_name a _ -> printName a
   B_seqmark a _ -> printSeqMark a

printBoolSent :: BOOL_SENT -> Doc
printBoolSent s = case s of
   Conjunction a _ -> text andS <+> (sep $ map printSentence a)
   Disjunction a _ -> text orS <+> (sep $ map printSentence a)
   Negation a _ -> text notS <+> printSentence a
   Implication a b _ -> text ifS <+> printSentence a <+> printSentence b
   Biconditional a b _ -> text iffS <+> printSentence a <+> printSentence b

printAtom :: ATOM -> Doc
printAtom s = case s of
   Equation a b _ -> br $ equals <+> printTerm a <+> printTerm b
   Atom t ts _ -> br $ printTerm t <+> printTermSeq ts

printTerm :: TERM -> Doc
printTerm s = case s of
   Name a _ -> printName a
   Funct_term _ _ _ -> text ""
   Comment_term _ _ _ -> text "" -- opt.

printTermSeq :: TERM_SEQ -> Doc
printTermSeq s = case s of
  Term_seq t _ -> fsep $ map printTerm t
  Seq_marks m _ -> fsep $ map printSeqMark m

printName :: NAME -> Doc
printName n = text $ tokStr n

printSeqMark :: SEQ_MARK -> Doc
printSeqMark m = text seqmark <> text (tokStr m)

-- parent
br :: Doc -> Doc
br a = lparen <> a <> rparen

-- keywords, reservednames in CLIF

seqmark :: String
seqmark = "..."

(...) :: String
(...) = "..."

orS :: String
orS = "or"

iffS :: String 
iffS = "iff"