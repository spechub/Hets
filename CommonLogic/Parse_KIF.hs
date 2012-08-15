{- |
Module      :  $Header$
Description :  Parser of the Knowledge Interchange Format
Copyright   :  (c) Karl Luc, DFKI Bremen 2010, Eugen Kuksa and Uni Bremen 2011, Soeren Schulze 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  s.schulze@uni-bremen.de
Stability   :  provisional
Portability :  portable
-}

module CommonLogic.Parse_KIF where

import qualified Common.AnnoState as AnnoState
import qualified Common.AS_Annotation as Annotation
import CommonLogic.AS_CommonLogic as AS
import Common.Id as Id
import Common.Keywords
import Common.Token

import CommonLogic.Lexer_KIF

import Text.ParserCombinators.Parsec as Parsec
import Control.Monad (liftM)

quantsent :: CharParser st SENTENCE
quantsent = do
  quant <- (key forallS <|> key existsS) <?> "quantifier"
  vars <- (parens $ many1 (pToken variable)) <?> "quantified variables"
  sent <- sentence
  return $ Quant_sent ((case tokStr quant of
                          s | s == forallS -> Universal
                          s | s == existsS -> Existential
                          _ -> error "Unknown quantifier in \"quantsent\"")
                       (map Name vars) sent)
    (Range (joinRanges [rangeSpan quant, rangeSpan vars, rangeSpan sent]))

logsent :: CharParser st SENTENCE
logsent = do
    c <- key andS <?> "conjunction"
    s <- many sentence -- joinRanges with s = []?
    return $ Bool_sent (Conjunction s) $ Range $ joinRanges [rangeSpan c,
             rangeSpan s]
  <|> do
    c <- key orS <?> "disjunction"
    s <- many sentence
    return $ Bool_sent (Disjunction s) $ Range $ joinRanges [rangeSpan c,
               rangeSpan s]
  <|> do
    c <- key notS <?> "negation"
    s <- sentence <?> "sentence after \"" ++ notS ++ "\""
    return $ Bool_sent (Negation s) $ Range $ joinRanges [rangeSpan c,
               rangeSpan s]
  <|> do
    c <- key equivS <?> "equivalence"
    s1 <- sentence <?> "sentence after \"" ++ equivS ++ "\""
    s2 <- sentence <?> "second sentence after \"" ++ equivS ++ "\""
    return $ Bool_sent (Biconditional s1 s2) $ Range $ joinRanges [rangeSpan c,
                                                   rangeSpan s1, rangeSpan s1]
  <|> do
    c <- key implS <?> "implication"
    s1 <- sentence <?> "sentence after \"" ++ implS ++ "\""
    s2 <- sentence <?> "second sentence after \"" ++ implS ++ "\""
    return $ Bool_sent (Implication s1 s2) $ Range $ joinRanges [rangeSpan c,
                                                   rangeSpan s1, rangeSpan s1]

equalAtom :: CharParser st ATOM
equalAtom = do
  key equalS
  t1 <- term <?> "term after \"" ++ equalS ++ "\""
  t2 <- term <?> "second term after \"" ++ equalS ++ "\""
  return $ Equation t1 t2

plainAtom :: CharParser st ATOM
plainAtom = do
  t <- pToken word <?> "word"
  return $ Atom (Name_term t) []

atomsent :: CharParser st ATOM -> CharParser st SENTENCE
atomsent = liftM (\a -> Atom_sent a $ Range $ rangeSpan a)

plainsent :: CharParser st SENTENCE
plainsent = atomsent plainAtom

parensent :: CharParser st SENTENCE
parensent = parens $ quantsent <|> logsent <|> relsent <|> eqsent <|> neqsent

funterm :: CharParser st TERM
funterm = do relword <- pToken (word <|> variable) <?> "funword"
             t <- many1 term
             return $ Funct_term (Name_term relword) (map Term_seq t)
               (Range $ joinRanges [rangeSpan relword, rangeSpan t])

relsent :: CharParser st SENTENCE
relsent = do
  Funct_term p args rn <- funterm
  return $ Atom_sent (Atom p args) rn

eqsent :: CharParser st SENTENCE
eqsent = atomsent equalAtom

neqsent :: CharParser st SENTENCE
neqsent = do
  key "/="
  t1 <- term <?> "term after \"/=\""
  t2 <- term <?> "second term after \"/=\""
  let eq = (Equation t1 t2)
  let rn = Range $ rangeSpan eq
  return $ Bool_sent (Negation (Atom_sent eq rn)) rn

term :: CharParser st TERM
term = liftM Name_term (pToken variable)
   <|> liftM Name_term (pToken word)
   <|> liftM Name_term (pToken quotedString)
   <|> liftM Name_term (pToken number)
   <|> parens funterm
--   <|> sentence

sentence :: CharParser st SENTENCE
sentence = parensent <|> plainsent

topLevelSentence :: CharParser st SENTENCE
topLevelSentence = notFollowedBy (foldr (<|>) pzero (map key terminatingKeywords))
                   >> sentence

basicSpec :: AnnoState.AParser st BASIC_SPEC
basicSpec = do
  many white
  sentences <- many topLevelSentence
  let phrases = map Sentence sentences
  let text = Text phrases $ Range $ joinRanges $ map rangeSpan phrases
  let text_meta = Text_meta text Nothing Nothing []
  let basic_items = Axiom_items [Annotation.emptyAnno text_meta]
  return $ Basic_spec [Annotation.emptyAnno basic_items]
