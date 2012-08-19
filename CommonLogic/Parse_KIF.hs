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
import Common.Lexer (notFollowedWith)
import Common.Token

import CommonLogic.Lexer_KIF

import Text.ParserCombinators.Parsec as Parsec
import Control.Monad (liftM)

boolop_unary :: [(String, SENTENCE -> BOOL_SENT, String)]
boolop_unary = [(notS, Negation, "negation")]

boolop_nary :: [(String, [SENTENCE] -> BOOL_SENT, String)]
boolop_nary = [(andS, Conjunction, "conjunction"),
               (orS, Disjunction, "disjunction")]

boolop_binary :: [(String, SENTENCE -> SENTENCE -> BOOL_SENT, String)]
boolop_binary = [(equivS, Biconditional, "equivalence"),
                 (implS, Implication, "implication")]

boolop_quant :: [(String, [NAME_OR_SEQMARK] -> SENTENCE -> QUANT_SENT, String)]
boolop_quant = [(forallS, Universal, "universal quantifier"),
                (existsS, Existential, "existiantial quantifier")]

parse_boolop :: [(String, op_t, String)] -> CharParser st (Token, op_t, String)
parse_boolop = choice . map
               (\(ident, con, desc) ->
                 liftM (\ch -> (ch, con, ident)) (key ident <?> desc))

logsent :: CharParser st SENTENCE
logsent = do (ch,con,ident) <- parse_boolop boolop_unary
             s <- sentence <?> "sentence after \"" ++ ident ++ "\""
             return $ Bool_sent (con s)
               $ Range $ joinRanges [rangeSpan ch, rangeSpan s]
      <|> do (ch,con,ident) <- parse_boolop boolop_nary
             s <- many sentence <?> "sentences after \"" ++ ident ++ "\""
             return $ Bool_sent (con s)
               $ Range $ joinRanges [rangeSpan ch, rangeSpan s]
      <|> do (ch,con,ident) <- parse_boolop boolop_binary
             s1 <- sentence <?> "first sentence after \"" ++ ident ++ "\""
             s2 <- sentence <?> "second sentence after \"" ++ ident ++ "\""
             return $ Bool_sent (con s1 s2)
               $ Range $ joinRanges [rangeSpan ch, rangeSpan s1, rangeSpan s2]
      <|> do (ch,con,ident) <- parse_boolop boolop_quant
             vars <- ((parens $ many1 (pToken variable))
                      <?> "quantified variables")
             s <- sentence <?> "sentence after \"" ++ ident ++ "\""
             return $ Quant_sent (con (map Name vars) s)
               $ Range $ joinRanges [rangeSpan ch, rangeSpan vars, rangeSpan s]

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
parensent = parens $ logsent <|> relsent <|> eqsent <|> neqsent

funterm :: CharParser st TERM
funterm = parens funterm
      <|> do relword <- pToken (word <|> variable) <?> "funword"
             let nt = Name_term relword
             t <- many term <?> "arguments"
             if null t
               then return nt
               else return $ Funct_term nt (map Term_seq t)
                    (Range $ joinRanges [rangeSpan relword, rangeSpan t])

relsent :: CharParser st SENTENCE
relsent = do
  ft <- funterm
  let a = case ft of
        p@(Name_term _) -> Atom p []
        Funct_term p args _ -> Atom p args
        _ -> error "unknown TERM in relsent"
  atomsent $ return a

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
topLevelSentence = notFollowedWith (return ())
                   (choice (map key terminatingKeywords))
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
