{- |
Module      :  ./CommonLogic/Parse_KIF.hs
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
import Common.Parsec (reserved)
import Common.Token
import Common.GlobalAnnotations (PrefixMap)

import CommonLogic.Lexer_KIF

import Text.ParserCombinators.Parsec as Parsec
import Control.Monad (liftM)

boolop_nary :: [(String, [SENTENCE] -> BOOL_SENT, String)]
boolop_nary = [(andS, Junction Conjunction, "conjunction"),
               (orS, Junction Disjunction, "disjunction")]

boolop_binary :: [(String, SENTENCE -> SENTENCE -> BOOL_SENT, String)]
boolop_binary = [(equivS, BinOp Biconditional, "equivalence"),
                 (implS, BinOp Implication, "implication")]

boolop_quant :: [(String, QUANT, String)]
boolop_quant = [(forallS, Universal, "universal quantifier"),
                (existsS, Existential, "existiantial quantifier")]

parse_keys :: [(String, op_t, String)] -> CharParser st (Token, op_t, String)
parse_keys = choice . map
             (\ (ident, con, desc) ->
               liftM (\ ch -> (ch, con, ident)) (key ident <?> desc))

logsent :: CharParser st SENTENCE
logsent = do ch <- key notS <?> "negation"
             s <- sentence <?> "sentence after \"" ++ notS ++ "\""
             return $ Bool_sent (Negation s)
               $ Range $ joinRanges [rangeSpan ch, rangeSpan s]
      <|> do (ch, con, ident) <- parse_keys boolop_nary
             s <- many sentence <?> "sentences after \"" ++ ident ++ "\""
             return $ Bool_sent (con s)
               $ Range $ joinRanges [rangeSpan ch, rangeSpan s]
      <|> do (ch, con, ident) <- parse_keys boolop_binary
             s1 <- sentence <?> "first sentence after \"" ++ ident ++ "\""
             s2 <- sentence <?> "second sentence after \"" ++ ident ++ "\""
             return $ Bool_sent (con s1 s2)
               $ Range $ joinRanges [rangeSpan ch, rangeSpan s1, rangeSpan s2]
      <|> do (ch, q, ident) <- parse_keys boolop_quant
             vars <- parens (many1 (liftM Name (pToken variable)
                                    <|> liftM SeqMark (pToken rowvar)))
                     <?> "quantified variables"
             s <- sentence <?> "sentence after \"" ++ ident ++ "\""
             return $ Quant_sent q vars s
               $ Range $ joinRanges [rangeSpan ch, rangeSpan vars, rangeSpan s]

plainAtom :: CharParser st ATOM
plainAtom = do
  t <- pToken (word <|> variable) <?> "word"
  return $ Atom (Name_term t) []

atomsent :: CharParser st ATOM -> CharParser st SENTENCE
atomsent = liftM (\ a -> Atom_sent a $ Range $ rangeSpan a)

plainsent :: CharParser st SENTENCE
plainsent = atomsent plainAtom

parensent :: CharParser st SENTENCE
parensent = parens $ logsent <|> relsent <|> eqsent

funterm :: CharParser st TERM
funterm = parens funterm
      <|> do relword <- pToken (reserved
               [equalS, neqS, andS, orS, equivS, implS, forallS, existsS, notS]
               (word <|> variable)) <?> "funword"
             let nt = Name_term relword
             t <- many (liftM Seq_marks (pToken rowvar)
                        <|> liftM Term_seq term) <?> "arguments"
             return $ if null t
               then nt
               else Funct_term nt t
                    (Range $ joinRanges [rangeSpan relword, rangeSpan t])

relsent :: CharParser st SENTENCE
relsent = do
  ft <- funterm
  let a = case ft of
        p@(Name_term _) -> Atom p []
        Funct_term p args _ -> Atom p args
        _ -> error "unknown TERM in relsent"
  atomsent $ return a

neqS :: String
neqS = "/="

eq_ops :: [(String, SENTENCE -> Id.Range -> SENTENCE, String)]
eq_ops = [(equalS, const, "equation"),
          (neqS, \ e rn -> Bool_sent (Negation e) rn, "inequality")]

eqsent :: CharParser st SENTENCE
eqsent = do
  (ch, con, ident) <- parse_keys eq_ops
  t1 <- term <?> "term after \"" ++ ident ++ "\""
  t2 <- term <?> "second term after \"" ++ ident ++ "\""
  let rn = Range $ joinRanges [rangeSpan ch, rangeSpan t1, rangeSpan t2]
  return $ con (Atom_sent (Equation t1 t2) rn) rn

term :: CharParser st TERM
term = liftM Name_term (pToken variable)
   <|> liftM Name_term (pToken word)
   <|> liftM Name_term (pToken quotedString)
   <|> liftM Name_term (pToken number)
   <|> parens (funterm <|> do
               s <- logsent <|> eqsent
               return $ That_term s $ Range $ rangeSpan s)

sentence :: CharParser st SENTENCE
sentence = parensent <|> plainsent

topLevelSentence :: CharParser st SENTENCE
topLevelSentence = notFollowedWith (return ())
                   (choice (map key terminatingKeywords))
                   >> sentence

basicSpec :: PrefixMap -> AnnoState.AParser st BASIC_SPEC
basicSpec _ = do
  many white
  sentences <- many topLevelSentence
  let phrases = map Sentence sentences
  let text = Text phrases $ Range $ joinRanges $ map rangeSpan phrases
  let text_meta = Text_meta text Nothing Nothing []
  let basic_items = Axiom_items [Annotation.emptyAnno text_meta]
  return $ Basic_spec [Annotation.emptyAnno basic_items]
