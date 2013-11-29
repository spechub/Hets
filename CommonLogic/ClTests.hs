{- |
Module      :  $Header$
Description :  Parser of common logic interface format
Copyright   :  (c) Karl Luc, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  kluc@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

-- Tests and examples of Common Logic AS and CLIF parse
-}


module CommonLogic.ClTests where

import CommonLogic.AS_CommonLogic
import CommonLogic.Parse_CLIF

import Common.Doc as Doc
import Common.Id as Id


import Text.ParserCombinators.Parsec


-- examples for abstract syntax

a :: NAME
a = Token "x" nullRange
b :: NAME
b = Token "y" nullRange
t1 :: TERM
t1 = Name_term a
t2 :: TERM
t2 = Name_term b
t3 :: TERM
t3 = Name_term (Token "P" nullRange)
t4 :: TERM
t4 = Name_term (Token "Q" nullRange)
ts1 :: TERM_SEQ
ts1 = Term_seq t1
b1 :: BOOL_SENT
b1 = Conjunction [s1, sa2]
b2 :: BOOL_SENT
b2 = Negation s1
b3 :: BOOL_SENT
b3 = Implication s1 s1

s1 :: SENTENCE
s1 = Atom_sent at1 nullRange
sa2 :: SENTENCE
sa2 = Atom_sent at2 nullRange
at1 :: ATOM
at1 = Atom t3 [Term_seq t1]
at2 :: ATOM
at2 = Atom t4 [Term_seq t2]
s2 :: SENTENCE
s2 = Bool_sent b1 nullRange
s3 :: SENTENCE
s3 = Bool_sent (Negation s1) nullRange
s4 :: SENTENCE
s4 = Bool_sent (Disjunction [s1, sa2]) nullRange

ct :: TERM
ct = Name_term (Token "Cat" nullRange)
{-
bs1 :: BINDING_SEQ
bs1 = B_name a nullRange
bs2 :: BINDING_SEQ
bs2 = B_name b nullRange
-}

-- examples for pretty printing

test :: Doc
test = Doc.text "Atom:" <+> printAtom at1
   $+$ Doc.text "Atom_sent:" <+> printSentence s1
   $+$ Doc.text "Bool_sent:" <+> printSentence s2
   $+$ Doc.text "Bool_sent:" <+> printSentence s4
   $+$ Doc.text "Bool_sent:" <+> printSentence s3
   $+$ Doc.text "Bool_sent:"
           <+> printSentence (Bool_sent (Implication s1 sa2) nullRange)
   $+$ Doc.text "Bool_sent:"
           <+> printSentence (Bool_sent (Biconditional s1 sa2) nullRange)
   $+$ Doc.text "Quant_sent:" <+> printSentence
       (Quant_sent (Existential [] s1) nullRange)
   $+$ Doc.text "Quant_sent:" <+> printSentence
       (Quant_sent (Universal [] s1) nullRange)
   $+$ Doc.text "Equation:" <+> printAtom (Equation t1 t1)
   $+$ Doc.text "Functional Term:" <+> printTerm (Funct_term t1 [ts1] nullRange)
   $+$ Doc.text "Sentence Functional:" <+> printSentence (
            Atom_sent (Atom (Funct_term t1 [ts1] nullRange)
                      [Term_seq t1]) nullRange)

-- examples for CLIF parser

p1 = parseTest sentence "(P x)"
p2 = parseTest sentence "(and (P x) (Q y))"
p3 = parseTest sentence "(or (Cat x) (Mat y))"
p4 = parseTest sentence "(not (On x y))"
p5 = parseTest sentence "(if (P x) (Q x))"

p6 = parseTest sentence "(exists (z) (and (Pet x) (Happy z) (Attr x z)))"


-- helper functions for testing sublogics

-- | parses the given string
abstrSyntax :: String -> Either ParseError TEXT_META
abstrSyntax = parse CommonLogic.Parse_CLIF.cltext ""

cParse p = parse p ""
