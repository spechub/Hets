{- |
Module      :  $Header$
Description :  Parser of common logic interface format
Copyright   :  Karl Luc, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.tx

Maintainer  :  kluc@informatik.uni-bremen.de
Stability   :  provisional
Portability :  

Parser of common logic interface format
-}

{-
  Ref.
  ISO/IEC IS 24707:2007(E)
-}

module CommonLogic.Parse_CLIF where

import CommonLogic.AS_CommonLogic
import Common.Id as Id
import Common.Doc as Doc
import Common.Lexer as Lexer
import Common.Parsec

import Text.ParserCombinators.Parsec as Parsec

-----------------------------------------------------------------------------------------

sentence :: CharParser st SENTENCE
sentence = do
  oParenT
  s <- sentence2
  cParenT
  return s

sentence2 :: CharParser st SENTENCE
sentence2 = do
  string "and"
  char ' '
  s <- many sentence
  return $ Bool_sent (Conjunction s nullRange) nullRange
  <|>
  do
    string "or"
    char ' '
    s <- many sentence
    return $ Bool_sent (Disjunction s nullRange) nullRange
  <|>
  do
    string "not"
    char ' '
    s <- sentence
    return $ Bool_sent (Negation s nullRange) nullRange
  <|>
  do
    string "if"
    char ' '
    s1 <- sentence
    s2 <- sentence
    return $ Bool_sent (Implication s1 s2 nullRange) nullRange
  <|>
  do
    string "iff"
    char ' '
    s1 <- sentence
    s2 <- sentence
    return $ Bool_sent (Biconditional s1 s2 nullRange) nullRange
  <|>
  do
    at <- atom
    return $ Atom_sent at nullRange

atom :: CharParser st ATOM
atom = do
  char '='
  char ' '
  t1 <- term
  t2 <- term
  return $ Equation t1 t2 nullRange
  <|>
  do
    t <- term
    ts <- termseq
    return $ Atom t ts nullRange

term :: CharParser st TERM
term = do
  t <- identifier
  return $ Name t nullRange

termseq :: CharParser st TERM_SEQ
termseq = do 
  s <- many term
  return $ Term_seq s nullRange

identifier :: CharParser st Id.Token
identifier = Lexer.pToken $ reserved reservedelement Lexer.scanAnyWords
  
reservedelement :: [String]
reservedelement = ["=", "and", "or", "iff", "if", "forall", "exists", "not"]