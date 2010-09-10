{- |
Module      :  $Header$
Description :  Parser of common logic interface format
Copyright   :  (c) Karl Luc, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  kluc@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Parser of common logic interface format
-}

{-
  Ref. Common Logic ISO/IEC IS 24707:2007(E)
-}

module CommonLogic.Parse_CLIF where

import qualified Common.AnnoState as AnnoState
import qualified Common.AS_Annotation as Annotation
import CommonLogic.AS_CommonLogic
import Common.Id as Id
import Common.Lexer as Lexer

import CommonLogic.Lexer_CLIF

import Text.ParserCombinators.Parsec as Parsec

-- | parser for cltext
cltext :: CharParser st TEXT
cltext = do
    nt <- try namedtext
    return nt
  <|> do
    t <- text
    return t

namedtext :: CharParser st TEXT
namedtext = parens $ do
    clTextKey
    n <- name
    t <- text
    return $ Named_text n t nullRange
  <|> do
    clTextKey
    n <- name
    return $ Named_text n (Text [] nullRange) nullRange

text :: CharParser st TEXT
text = do
    phr <- many1 phrase
    return $ Text phr nullRange

-- remove the try
-- keys set here to prevent try in more complex parser to get the right
-- error message in ex. the following text
phrase :: CharParser st PHRASE
phrase = do
    try (string "(cl-module")
    spaces
    m <- pModule
    cParenT
    return $ Module m
    <|> do
    try (string "(cl-imports")
    spaces
    i <- importation
    cParenT
    return $ Importation i
    <|> do
    try (string "(cl-comment")
    spaces
    (c,t) <- comment <?> "comment: 3"
    cParenT
    return $ Comment_text c t nullRange
    <|> do
      s <- sentence
      return $ Sentence s

-- | parser for module
pModule :: CharParser st MODULE
pModule = do
  -- clModuleKey
  t <- identifier
  txt <- text
  return $ Mod t txt nullRange
 <|> do
  -- clModuleKey
  t <- identifier -- TODO
  return $ Mod t (Text [] nullRange) nullRange

importation :: CharParser st IMPORTATION
importation = do
     -- clImportsKey
     n <- identifier
     return $ Imp_name n

comment :: CharParser st (COMMENT, TEXT)
comment = do
   -- clCommentKey <?> "nothing"
   qs <- quotedstring <|> enclosedname
   -- t <- text <?> "Text" -- TODO empty Text
   return $ (Comment qs nullRange, Text [] nullRange)
  <|> do
   -- clCommentKey
   qs <- quotedstring <|> enclosedname
   return $ (Comment qs nullRange, (Text [] nullRange))

-- | parser for sentences
sentence :: CharParser st SENTENCE
sentence = parens $ do
  at <- atom <?> "predicate"
  return $ Atom_sent at $ Range $ rangeSpan at
  <|> do 
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
    s <- sentence
    return $ Bool_sent (Negation s) $ Range $ joinRanges [rangeSpan c,
               rangeSpan s]
  <|> do
    c <- try iffKey -- with try? yes.
    s1 <- sentence
    s2 <- sentence
    return $ Bool_sent (Biconditional s1 s2) $ Range $ joinRanges [rangeSpan c,
                                                   rangeSpan s1, rangeSpan s1]
  <|> do
    c <- ifKey
    s1 <- sentence
    s2 <- sentence
    return $ Bool_sent (Implication s1 s2) $ Range $ joinRanges [rangeSpan c,
                                                   rangeSpan s1, rangeSpan s1]
  <|> do
    c <- forallKey
    bs <- parens bindingseq
    s <- sentence
    return $ Quant_sent (Universal bs s) $ Range $ joinRanges [rangeSpan c,
               rangeSpan bs, rangeSpan s]
  <|> do
    c <- existsKey
    bs <- parens bindingseq
    s <- sentence
    return $ Quant_sent (Existential bs s) $ Range $ joinRanges [rangeSpan c,
               rangeSpan s]

bindingseq :: CharParser st [NAME_OR_SEQMARK]
bindingseq = many $ do
    s <- seqmark -- fix seqmark parser for one
    return $ SeqMark s
  <|> do
    n <- identifier
    return $ Name n

atom :: CharParser st ATOM
atom = do
    Lexer.pToken $ string "="
    t1 <- term
    t2 <- term
    return $ Equation t1 t2
  <|> do
    t <- term
    ts <- many1 termseq
    return $ Atom t ts

term :: CharParser st TERM
term = do
     t <- identifier
     return $ Name_term t
   <|> do
     parens $ do
       t <- term
       ts <- many1 termseq -- many1?
       return $ Funct_term t ts $ Range $ joinRanges [rangeSpan t
                                                      , rangeSpan ts]

termseq :: CharParser st TERM_SEQ
termseq = do
  x <- seqmark
  return $ Seq_marks $ x
  <|> do
   t <- term
   return $ Term_seq t

-- | Toplevel parser for basic specs
basicSpec :: AnnoState.AParser st BASIC_SPEC
basicSpec =
  fmap Basic_spec (AnnoState.annosParser parseBasicItems)
  <|> (Lexer.oBraceT >> Lexer.cBraceT >> return (Basic_spec []))

-- function to parse different syntaxes
-- parsing: axiom items with dots, clif sentences, clif text
-- first getting only the sentences
parseBasicItems :: AnnoState.AParser st BASIC_ITEMS
parseBasicItems = parseAxItems
              <|> try parseSentences
              <|> parseClText
              -- parseClText

parseSentences :: AnnoState.AParser st BASIC_ITEMS
parseSentences = do
    xs <- many1 aFormula
    return $ Axiom_items xs

-- FIX
parseClText :: AnnoState.AParser st BASIC_ITEMS
parseClText = do 
  tx <- cltext
  return $ Axiom_items (senToAn (senOfText tx))

{-
parseClText :: AnnoState.AParser st BASIC_ITEMS
parseClText = do
     tx <- pModule
     return $ Axiom_items (senToAn (ps tx))

ps :: MODULE -> [SENTENCE]
ps (Mod _ tx _) = senOfText tx
ps (Mod_ex _ _ _ _) = []
-}

senToAn :: [SENTENCE] -> [Annotation.Annoted SENTENCE]
senToAn x = map (\y -> Annotation.Annoted y nullRange [] []) x

senOfText :: TEXT -> [SENTENCE]
senOfText (Text phr _) = foldl (sen2) [] phr
senOfText (Named_text _ t _) = senOfText t

sen2 :: [SENTENCE] -> PHRASE -> [SENTENCE]
sen2 s p = case p of
   Sentence x -> s ++ [x]
   Module m -> case m of
                 Mod _ t _ -> s ++ (senOfText t)
                 Mod_ex _ _ t _ -> s ++ (senOfText t) -- TODO
   Comment_text _ t _ -> s ++ (senOfText t)
   _ -> s -- TODO importation

-- if (isSen p) then (s ++ [senOfPhr p]) else s

senOfPhr :: PHRASE -> SENTENCE
senOfPhr (Sentence s) = s
-- senOfPhr (Module m) = case m of
--    Mod name text id -> 
--    Mod_ex name names text id -> 
senOfPhr _ = Atom_sent (Atom (Name_term (Token "empty" nullRange)) [])
               nullRange

isSen :: PHRASE -> Bool
isSen (Sentence _) = True
isSen _ = False

-- | parser for Axiom_items
parseAxItems :: AnnoState.AParser st BASIC_ITEMS
parseAxItems = do
       d <- AnnoState.dotT
       (fs, ds) <- aFormula `Lexer.separatedBy` AnnoState.dotT
       (_, an) <- AnnoState.optSemi
       let _ = Id.catRange (d : ds)
           ns = init fs ++ [Annotation.appendAnno (last fs) an]
       return $ Axiom_items ns

-- | Toplevel parser for formulae
aFormula :: AnnoState.AParser st (Annotation.Annoted SENTENCE)
aFormula = do
     AnnoState.allAnnoParser sentence

-- | collect all the names and sequence markers
symbItems :: GenParser Char st NAME
symbItems = do
  return (Token "x" nullRange)
