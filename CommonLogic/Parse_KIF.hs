module CommonLogic.Parse_KIF where

import qualified Common.AnnoState as AnnoState
import qualified Common.AS_Annotation as Annotation
import CommonLogic.AS_CommonLogic as AS
import Common.Id as Id
import Common.Parsec

import CommonLogic.Lexer_KIF

import Text.ParserCombinators.Parsec as Parsec
import Control.Monad (liftM)

quantsent :: CharParser st SENTENCE
quantsent = do
  quant <- (string "forall" <|> string "exists") <?> "quantifier"
  many1 white
  vars <- (parens $ many1 (pToken variable)) <?> "quantified variables"
  sent <- sentence
  return $ Quant_sent ((case quant of
                          "forall" -> Universal
                          "exists" -> Existential
                          _ -> error "Unknown quantifier")
                       (map Name vars) sent)
    (Range (joinRanges [rangeSpan quant,
                                             rangeSpan vars,
                                             rangeSpan sent]))

logsent :: CharParser st SENTENCE
logsent = do
    c <- andKey
    s <- many sentence -- joinRanges with s = []?
    return $ Bool_sent (Conjunction s) $ Range $ joinRanges [rangeSpan c,
             rangeSpan s]
  <|> do
    c <- orKey
    s <- many sentence
    return $ Bool_sent (Disjunction s) $ Range $ joinRanges [rangeSpan c,
               rangeSpan s]
  <|> do
    c <- notKey
    s <- sentence <?> "sentence after \"not\""
    return $ Bool_sent (Negation s) $ Range $ joinRanges [rangeSpan c,
               rangeSpan s]
  <|> do
    c <- try iffKey
    s1 <- sentence <?> "sentence after \"<=>\""
    s2 <- sentence <?> "second sentence after \"<=>\""
    return $ Bool_sent (Biconditional s1 s2) $ Range $ joinRanges [rangeSpan c,
                                                   rangeSpan s1, rangeSpan s1]
  <|> do
    c <- ifKey
    s1 <- sentence <?> "sentence after \"=>\""
    s2 <- sentence <?> "second sentence after \"=>\""
    return $ Bool_sent (Implication s1 s2) $ Range $ joinRanges [rangeSpan c,
                                                   rangeSpan s1, rangeSpan s1]

atom :: CharParser st ATOM
atom = try (do
    oParenT
    equalsKey
    t1 <- term <?> "term after \"=\""
    t2 <- term <?> "second term after \"=\""
    cParenT
    return $ Equation t1 t2)
  <|> do
    t <- pToken (reserved ["end"] word) <?> "word"
    return $ Atom (Name_term t) []

atomsent :: CharParser st SENTENCE
atomsent = do
  a <- atom
  return $ Atom_sent a $ Range $ rangeSpan a

funterm :: CharParser st TERM
funterm = parens (do relword <- pToken word <?> "funword"
                     t <- many1 term
                     return $ Funct_term (Name_term relword) (map Term_seq t)
                       (Range $ joinRanges [rangeSpan relword, rangeSpan t]))

relsent :: CharParser st SENTENCE
relsent = do
  Funct_term p args rn <- funterm
  return $ Atom_sent (Atom p args) rn

neqsent :: CharParser st SENTENCE
neqsent = do
  oParenT
  notEqualKey
  t1 <- term <?> "term after \"/=\""
  t2 <- term <?> "second term after \"/=\""
  cParenT
  let eq = (Equation t1 t2)
  let rn = Range $ rangeSpan eq
  return $ Bool_sent (Negation (Atom_sent eq rn)) rn

term :: CharParser st TERM
term = try (liftM Name_term (pToken variable))
   <|> try (liftM Name_term (pToken word))
   <|> try (liftM Name_term (pToken quotedString))
   <|> try funterm
   <|> try (liftM Name_term (pToken number))
--   <|> try sentence

sentence :: CharParser st SENTENCE
sentence =
  try (parens quantsent)
   <|> try (parens logsent)
   <|> try relsent
   <|> try atomsent
   <|> neqsent

basicSpec :: AnnoState.AParser st BASIC_SPEC
basicSpec = do
  many white
  sentences <- many sentence
  let phrases = map Sentence sentences
  let text = Text phrases $ Range $ joinRanges $ map rangeSpan phrases
  let text_meta = Text_meta text Nothing Nothing []
  let basic_items = Axiom_items [Annotation.emptyAnno text_meta]
  return $ Basic_spec [Annotation.emptyAnno basic_items]
