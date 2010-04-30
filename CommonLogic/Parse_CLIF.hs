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

import qualified Common.AnnoState as AnnoState
import qualified Common.AS_Annotation as Annotation
import CommonLogic.AS_CommonLogic
import Common.Id as Id
import Common.Lexer as Lexer
import Common.Parsec
import Common.Keywords

import Text.ParserCombinators.Parsec as Parsec
import Data.Char (ord)

----------------------------------------------------------------------------
                
-- parser for sentences
sentence :: CharParser st SENTENCE
sentence = parens $ do
  at <- atom
  return $ Atom_sent at $ Range $ rangeSpan at
  <|>
  do
  c <- andKey
  s <- many1 sentence
  return $ Bool_sent (Conjunction s) $ Range $ joinRanges [rangeSpan c, rangeSpan s]
  <|>
  do
    c <- orKey
    s <- many1 sentence
    return $ Bool_sent (Disjunction s) $ Range $ joinRanges [rangeSpan c, rangeSpan s]
  <|>
  do
    c <- notKey
    s <- sentence
    return $ Bool_sent (Negation s) $ Range $ joinRanges [rangeSpan c, rangeSpan s]
  <|>
  do
    c <- try iffKey
    s1 <- sentence
    s2 <- sentence
    return $ Bool_sent (Biconditional s1 s2) $ Range $ joinRanges [rangeSpan c, 
                                                   rangeSpan s1, rangeSpan s1]
  <|>
   do
    c <- ifKey
    s1 <- sentence
    s2 <- sentence
    return $ Bool_sent (Implication s1 s2) $ Range $ joinRanges [rangeSpan c, 
                                                   rangeSpan s1, rangeSpan s1]
  <|>
  do
    c <- forallKey
    bs <- parens bindingseq
    s <- sentence
    return $ Quant_sent (Universal bs s) $ Range $ joinRanges [rangeSpan c, rangeSpan bs,
                                                               rangeSpan s]
  <|>
  do 
    c <- existsKey
    bs <- parens bindingseq
    s <- sentence
    return $ Quant_sent (Existential bs s) $ Range $ joinRanges [rangeSpan c, rangeSpan s]


bindingseq :: CharParser st [NAME_OR_SEQMARK]
bindingseq = many $ do 
  n <- identifier
  return $ Name n

atom :: CharParser st ATOM
atom = do
  Lexer.pToken $ string "="
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
      return $ Funct_term t ts $ Range $ joinRanges [rangeSpan t, rangeSpan ts]

termseq :: CharParser st TERM_SEQ
termseq = do 
  s <- many term
  return $ Term_seq s $ Range $ joinRanges [rangeSpan s]  

-------

text :: CharParser st TEXT
text = do
    phr <- try $ many phrase
    return $ Text phr $ if phr == [] then nullRange else nullRange
  <|> do
    m <- pModule
    return $ Text [Module m] nullRange
  <|> do
    oParenT
    clTextKey
    n <- name
    t <- text
    cParenT
    return $ Named_text n t nullRange

name :: CharParser st String
name = string "name"

phrase :: CharParser st PHRASE
phrase = do 
  s <- sentence
  return $ Sentence s

pModule :: CharParser st MODULE
pModule = parens $ do
  clModuleKey
  t <- identifier
  ts <- many identifier
  txt <- text
  return $ Mod t ts txt nullRange

importation :: CharParser st IMPORTATION
importation = do 
     return $ Imp_name (Token "" nullRange)

comment :: CharParser st COMMENT
comment = do
   clCommentKey
   return $ Comment "" nullRange

-- file parser
f1 :: IO ()
f1 = do x <- readFile "CommonLogic/fp.clf"
        parseTest sentence x

f2 :: Either ParseError SENTENCE
f2 = runParser sentence "" "" "(P x)"

parseTestFile :: String -> IO ()
parseTestFile f = do x <- readFile f
                     parseTest (many sentence) x

-- | parser for parens
parens :: CharParser st a -> CharParser st a
parens p = do 
   spaces
   oParenT >> p << cParenT

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

-- cl keys
clTextKey :: CharParser st Id.Token
clTextKey = Lexer.pToken $ string "cl:text"

clModuleKey :: CharParser st Id.Token
clModuleKey = Lexer.pToken $ string "cl:module"

clImportsKey :: CharParser st Id.Token
clImportsKey = Lexer.pToken $ string "cl:imports"

clExcludesKey :: CharParser st Id.Token
clExcludesKey = Lexer.pToken $ string "cl:excludes"

clCommentKey :: CharParser st Id.Token
clCommentKey = Lexer.pToken $ string "cl:comment"
            
identifier :: CharParser st Id.Token
identifier = Lexer.pToken $ reserved reservedelement $ scanClWord

scanClWord :: CharParser st String
scanClWord = many1 clLetter <?> "words"

clLetters :: Char -> Bool
clLetters ch = let c = ord ch in
   if c >= 33 && c <= 126 then c <= 38 && c /= 34 || c >= 42 && c /= 64 && c /= 92
   else False

-- a..z, A..z, 0..9, ~!#$%^&*_+{}|:<>?`-=[];,.

clLetter :: CharParser st Char
clLetter = satisfy clLetters <?> "cl letter"

reservedelement :: [String]
reservedelement = ["=", "and", "or", "iff", "if", "forall", "exists", "not", "...", 
                   "cl:text", "cl:imports", "cl:excludes", "cl:module", "cl:comment",
                   "roleset:"]

----------------------------------------------------------------------------

-- | Toplevel parser for basic specs
basicSpec :: AnnoState.AParser st BASIC_SPEC
basicSpec =
  fmap Basic_spec (AnnoState.annosParser parseBasicItems)
  <|> (Lexer.oBraceT >> Lexer.cBraceT >> return (Basic_spec []))

-- | Parser for basic items
parseBasicItems :: AnnoState.AParser st BASIC_ITEMS
parseBasicItems = parseAxItems

{-
-- | parser for predicate declarations
parsePredDecl :: AnnoState.AParser st BASIC_ITEMS
parsePredDecl = fmap P_decl 
-}

-- | parser for Axiom_items
parseAxItems :: AnnoState.AParser st BASIC_ITEMS
parseAxItems = do
       d <- AnnoState.dotT
       (fs, ds) <- aFormula `Lexer.separatedBy` AnnoState.dotT
       (_, an) <- AnnoState.optSemi
       let _  = Id.catRange (d:ds)
           ns = init fs ++ [Annotation.appendAnno (last fs) an]
       return $ Axiom_items ns

-- | Toplevel parser for formulae
aFormula :: AnnoState.AParser st (Annotation.Annoted SENTENCE)
aFormula =  AnnoState.allAnnoParser sentence

-- | collect all the names and sequence markers
symbItems :: GenParser Char st NAME
symbItems = do
  return (Token "" nullRange)