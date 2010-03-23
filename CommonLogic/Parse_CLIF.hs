{- |
Module      :  $Header$
Description :  Parser of common logic interface format
Copyright   :  (c) Karl Luc, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  kluc@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Parser of common logic interface format
-}

{-
  Ref. ISO/IEC IS 24707:2007(E)
-}

module CommonLogic.Parse_CLIF where

import CommonLogic.AS_CommonLogic
import Common.Id as Id
import Common.Lexer as Lexer
import Common.Parsec
import Common.Keywords

import Text.ParserCombinators.Parsec as Parsec

----------------------------------------------------------------------------

instance GetRange SENTENCE where
  getRange = sentenceRange

sentenceRange :: SENTENCE -> Range
sentenceRange x = case x of
                    Atom_sent y z -> z
                    Bool_sent y z -> z
                    Quant_sent y z -> z

lastRange :: Range -> Range
lastRange (Range x) = Range [last x]

keySentRange :: Token -> SENTENCE -> Range
keySentRange x s = appRange (getRange x) (lastRange $ getRange s)

-- parser for sentences
sentence :: CharParser st SENTENCE
sentence = parens $ do
  c <- andKey
  s <- many sentence
  return $ Bool_sent (Conjunction s) $  keySentRange c (last s)
  <|>
  do
    c <- orKey
    s <- many sentence
    return $ Bool_sent (Disjunction s) $ keySentRange c (last s)
  <|>
  do
    c <- notKey
    s <- sentence
    return $ Bool_sent (Negation s) $ keySentRange c s
  <|>
  do
    c <- ifKey
    s1 <- sentence
    s2 <- sentence
    return $ Bool_sent (Implication s1 s2) $ keySentRange c s2
  <|>
  do
    c <- iffKey
    s1 <- sentence
    s2 <- sentence
    return $ Bool_sent (Biconditional s1 s2) $ keySentRange c s2
  <|>
  do
    c <- forallKey
    bs <- parens bindingseq
    s <- sentence
    return $ Quant_sent (Universal bs s) $ keySentRange c s
  <|>
  do 
    c <- existsKey
    bs <- parens bindingseq
    s <- sentence
    return $ Quant_sent (Existential bs s) $ keySentRange c s
  <|>
  do
    at <- atom
    return $ Atom_sent at $ appRange (case at of
                                         Atom t ts -> case t of 
                                                        Name x r -> r)
                                     (case at of 
                                         Atom t ts -> case ts of
                                                        Term_seq x r -> lastRange r)

bindingseq :: CharParser st [BINDING_SEQ]
bindingseq = many $ do 
  n <- identifier
  return $ B_name n $ getRange n

atom :: CharParser st ATOM
atom = do
  c <- Lexer.pToken $ string "="
  t1 <- term
  t2 <- term
  return $ Equation t1 t2
  <|>
  do
    t <- term
    ts <- termseq
    return $ Atom t ts

term :: CharParser st TERM
term = do
  t <- identifier
  return $ Name t $ tokPos t
  <|>
  do 
    parens $ do 
      t <- term
      ts <- termseq
      return $ Funct_term t ts nullRange

termseq :: CharParser st TERM_SEQ
termseq = do 
  s <- many term
  return $ Term_seq s $ appRange (case (head s) of
                                    Name x r -> r) -- missing pm
                                 (case (last s) of
                                    Name x r -> r)

parens :: CharParser st a -> CharParser st a
parens p = oParenT >> p << cParenT

-- Parser Keywords
andKey :: CharParser st Id.Token
andKey = Lexer.pToken $ string andS

notKey :: CharParser st Id.Token
notKey = Lexer.pToken $ string notS

orKey :: CharParser st Id.Token
orKey = Lexer.pToken $ string orS

ifKey :: CharParser st Id.Token
ifKey = Lexer.pToken $ string ifS

iffKey :: CharParser st Id.Token
iffKey = Lexer.pToken $ string iffS

forallKey :: CharParser st Id.Token
forallKey = Lexer.pToken $ string forallS

existsKey :: CharParser st Id.Token
existsKey = Lexer.pToken $ string existsS

-- change to enable digits
identifier :: CharParser st Id.Token
identifier = Lexer.pToken $ reserved reservedelement Lexer.scanAnyWords

reservedelement :: [String]
reservedelement = ["=", "and", "or", "iff", "if", "forall", "exists", "not", "..."]