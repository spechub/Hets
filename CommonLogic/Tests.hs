-- Tests and examples of Common Logic AS and CLIF parse

module CommonLogic.Tests where

import CommonLogic.AS_CommonLogic
import CommonLogic.Parse_CLIF

import Common.Doc
import Common.Id as Id

import Text.ParserCombinators.Parsec

-----------------------------------------------------------------------

-- examples for abstract syntax

a :: NAME
a = Token "x" nullRange
b :: NAME
b = Token "y" nullRange
t1 :: TERM
t1 = Name a nullRange
t2 :: TERM
t2 = Name b nullRange
t3 :: TERM
t3 = Name (Token "P" nullRange) nullRange
t4 :: TERM
t4 = Name (Token "Q" nullRange) nullRange
ts1 :: TERM_SEQ
ts1 = Term_seq [t1, t1, t2] nullRange
b1 :: BOOL_SENT
b1 = Conjunction [s1, sa2] nullRange
b2 :: BOOL_SENT
b2 = Negation s1 nullRange
b3 :: BOOL_SENT
b3 = Implication s1 s1 nullRange

s1 :: SENTENCE 
s1 = Atom_sent at1 nullRange
sa2 :: SENTENCE
sa2 = Atom_sent at2 nullRange
at1 :: ATOM
at1 = Atom t3 (Term_seq [t1] nullRange) nullRange
at2 :: ATOM
at2 = Atom t4 (Term_seq [t2] nullRange) nullRange
s2 :: SENTENCE
s2 = Bool_sent b1 nullRange
s3 :: SENTENCE
s3 = Bool_sent (Negation s1 nullRange) nullRange
s4 :: SENTENCE
s4 = Bool_sent (Disjunction [s1, sa2] nullRange) nullRange

ct :: TERM
ct = Name (Token "Cat" nullRange) nullRange
bs1 :: BINDING_SEQ
bs1 = B_name a nullRange
bs2 :: BINDING_SEQ
bs2 = B_name b nullRange

-- examples for pretty printing

test :: Doc
test = text "Atom:" <+> printAtom at1 
   $+$ text "Atom_sent:" <+> printSentence s1 
   $+$ text "Bool_sent:" <+> printSentence s2
   $+$ text "Bool_sent:" <+> printSentence s4
   $+$ text "Bool_sent:" <+> printSentence s3
   $+$ text "Bool_sent:" <+> printSentence (Bool_sent (Implication s1 sa2 nullRange) nullRange)
   $+$ text "Bool_sent:" <+> printSentence (Bool_sent (Biconditional s1 sa2 nullRange) nullRange)
   $+$ text "Quant_sent:" <+> printSentence 
       (Quant_sent (Existential [bs1, bs2] s1 nullRange) nullRange)
   $+$ text "Quant_sent:" <+> printSentence 
       (Quant_sent (Universal [bs1, bs2] s1 nullRange) nullRange)
   $+$ text "Equation:" <+> printAtom (Equation t1 t1 nullRange)


-- examples for CLIF parser

p1 = parseTest sentence "(P x)"
p2 = parseTest sentence "(and (P x) (Q y))"
p3 = parseTest sentence "(or (Cat x) (Mat y))"
p4 = parseTest sentence "(not (On x y))"
p5 = parseTest sentence "(if (P x) (Q x))"