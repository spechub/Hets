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
                                                        Name_term x -> getRange x)
                                     (case at of 
                                         Atom t ts -> case ts of
                                                        Term_seq x r -> lastRange r)

bindingseq :: CharParser st [NAME_OR_SEQMARK]
bindingseq = many $ do 
  n <- identifier
  return $ Name n

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
  return $ Name_term t
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
                                    Name_term x -> getRange x) -- missing pm
                                 (case (last s) of
                                    Name_term x -> getRange x)

text :: CharParser st TEXT
text = do
  c <- Lexer.pToken $ string "cl_text"
  phr <- many phrase
  return $ Text phr $ if phr == [] then tokPos c else 
                                   appRange (tokPos c) (case (last phr) of
                                     Module _ r -> lastRange r
                                     Sentence _ r -> lastRange r
                                     Importation _ r -> lastRange r
                                     Comment_Text _ _ r -> lastRange r)

phrase :: CharParser st PHRASE
phrase = do
  (m, r) <- try $ parens $ do 
               c <- Lexer.pToken $ string "cl_module"
               t <- identifier
               ts <- many identifier
               txt <- text
               return $ (Mod t ts txt, appRange (tokPos c) (case txt of
                                                              Text _ x -> lastRange x))
  return $ Module m r
  <|> do 
    m <- sentence
    return $ Sentence m $ getRange m

pModule :: CharParser st MODULE
pModule = parens $ do
  c <- Lexer.pToken $ string "cl_module"
  t <- identifier
  ts <- many identifier
  txt <- text
  return $ Mod t ts txt

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
reservedelement = ["=", "and", "or", "iff", "if", "forall", "exists", "not", "...",
                   "cl_text", "cl_imports", "cl_excludes", "cl_module", "cl_comment"]