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
import Common.Parsec
import Common.Keywords

import Text.ParserCombinators.Parsec as Parsec
import Data.Char (ord, isSpace)

----------------------------------------------------------------------------
                
-- parser for sentences
sentence :: CharParser st SENTENCE
sentence = parens $ do
  at <- try atom
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
    s <- seqmark -- fix seqmark parser for one
    return $ SeqMark s
  <|> do
    n <- identifier
    return $ Name n

atom :: CharParser st ATOM
atom = do
  -- Lexer.pToken $ string "="
  string "="
  many1 space
  t1 <- term
  t2 <- term
  return $ Equation t1 t2
  <|>
  do
    t <- term
    ts <- many1 termseq
    return $ Atom t ts

term :: CharParser st TERM
term = do
    t <- identifier
    return $ Name_term t
  <|>
  do 
    parens $ do 
      n <- Lexer.pToken (string "not") -- dirty kif, fix
      ts <- many1 termseq
      return $ Funct_term (Name_term n) ts $ Range $ joinRanges [rangeSpan n, rangeSpan ts]
      <|> do 
      t <- term
      ts <- many1 termseq
      return $ Funct_term t ts $ Range $ joinRanges [rangeSpan t, rangeSpan ts]

termseq :: CharParser st TERM_SEQ
termseq = do 
  x <- seqmark
  return $ Seq_marks $ x
  <|> do
   t <- term
   return $ Term_seq t

-------

-- text remove -> cltext = { phrase }
text :: CharParser st TEXT
text = do
    phr <- many1 phrase
    return $ Text phr nullRange
{-
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
-}

name :: CharParser st String
name = do 
        x <- identifier
        return $ (tokStr x)

phrase :: CharParser st PHRASE
phrase = do 
    s <- try sentence
    return $ Sentence s
  <|> do
    m <- try pModule
    return $ Module m
  <|> do
    i <- try importation
    return $ Importation i
  <|> do
    (c,t) <- comment
    return $ Comment_text c t nullRange

-- | parser for module
pModule :: CharParser st MODULE
pModule = parens $ do
  clModuleKey
  t <- identifier
  txt <- text
  return $ Mod t txt nullRange

importation :: CharParser st IMPORTATION
importation = parens $ do 
     clImportsKey
     n <- identifier
     return $ Imp_name n

comment :: CharParser st (COMMENT, TEXT)
comment = parens $ do 
   clCommentKey
   qs <- quotedstring
   t <- many text
   return $ (Comment qs nullRange, if t == [] then Text [] nullRange else head t)

quotedstring :: CharParser st String
quotedstring = do 
   char '\''
   s <- (many $ (satisfy clLetters2) <|> (oneOf whitec) <|> char '(' <|> char ')' <|> char '\"') 
            <?> "quotedstring: word"
   char '\''
   return $ s

enclosedname :: CharParser st String
enclosedname = do
   char '\"'
   s <- (many $ (satisfy clLetters2) <|> (oneOf whitec) <|> char '(' <|> char ')' <|> char '\'') 
         <?> "word"
   char '\"' <?> "\""
   return s

-- 
f1 :: Either ParseError SENTENCE
f1 = runParser sentence "" "" "(P x)"

parseTestFile :: String -> IO ()
parseTestFile f = do x <- readFile f
                     parseTest text x

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
ifKey = (Lexer.pToken $ string ifS) <|> (Lexer.pToken $ string "=>")

iffKey :: CharParser st Id.Token
iffKey = (Lexer.pToken $ string iffS) <|> (Lexer.pToken $ string "<=>")

forallKey :: CharParser st Id.Token
forallKey = Lexer.pToken $ string forallS

existsKey :: CharParser st Id.Token
existsKey = Lexer.pToken $ string existsS

-- cl keys
clTextKey :: CharParser st Id.Token
clTextKey = Lexer.pToken $ try (string "cl:text") <|> string "cl-text"

clModuleKey :: CharParser st Id.Token
clModuleKey = Lexer.pToken $ try (string "cl:module") <|> string "cl-module"

clImportsKey :: CharParser st Id.Token
clImportsKey = Lexer.pToken $ try (string "cl:imports") <|> string "cl-imports"

clExcludesKey :: CharParser st Id.Token
clExcludesKey = Lexer.pToken $ try (string "cl:excludes") <|> string "cl-excludes"

clCommentKey :: CharParser st Id.Token
clCommentKey = Lexer.pToken $ try (string "cl:comment") <|> string "cl-comment"
            
seqmark :: CharParser st Id.Token
seqmark = Lexer.pToken $ reserved reservedelement2 $ scanSeqMark

identifier :: CharParser st Id.Token
identifier = Lexer.pToken $ reserved reservedelement $ scanClWord

scanSeqMark :: CharParser st String
scanSeqMark = do
           sq <- string "..." <|> string "@" -- kif @
           w <- many clLetter <?> "sequence marker"
           return $ sq ++ w

scanClWord :: CharParser st String
scanClWord = quotedstring <|> enclosedname <|> (many1 clLetter <?> "words")

clLetters :: Char -> Bool
clLetters ch = let c = ord ch in
   if c >= 33 && c <= 126 then c <= 38 && c /= 34 || c >= 42 && c /= 64 && c /= 92
   else False

clLetters2 :: Char -> Bool
clLetters2 ch = let c = ord ch in
   if c >= 32 && c <= 126 then c <= 38 && c /= 34 || c >= 42 && c /= 64 && c /= 92
   else False

-- a..z, A..z, 0..9, ~!#$%^&*_+{}|:<>?`-=[];,.

clLetter :: CharParser st Char
clLetter = satisfy clLetters <?> "cl letter"

reservedelement :: [String]
reservedelement = ["=", "and", "or", "iff", "if", "forall", "exists", "not", "...", 
                   "cl:text", "cl:imports", "cl:excludes", "cl:module", "cl:comment",
                   "roleset:"] ++ reservedcl ++ reservedkif

reservedcl :: [String]
reservedcl = ["cl-text", "cl-imports", "cl-exlcudes", "cl-module", "cl-comment"]

reservedkif :: [String]
reservedkif = ["<=>", "=>", "<="]

reservedelement2 :: [String]
reservedelement2 = ["=", "and", "or", "iff", "if", "forall", "exists", "not", 
                   "cl:text", "cl:imports", "cl:excludes", "cl:module", "cl:comment",
                   "roleset:", "<=>", "=>", "<="]

whitec :: String
whitec = "\n\r\t\v\f "

white :: CharParser st String
white = many1 $ oneOf whitec

----------------------------------------------------------------------------

-- | Toplevel parser for basic specs
basicSpec :: AnnoState.AParser st BASIC_SPEC
basicSpec =
  fmap Basic_spec (AnnoState.annosParser parseBasicItems)
  <|> (Lexer.oBraceT >> Lexer.cBraceT >> return (Basic_spec []))


-- function to parse different syntaxes
-- parsing: axiom items with dots, clif sentences, clif text, kif
-- first getting only the sentences
parseBasicItems :: AnnoState.AParser st BASIC_ITEMS
parseBasicItems = parseAxItems
              <|> try parseSentences
              <|> try parseClText
              -- <|> try parseKif

parseSentences :: AnnoState.AParser st BASIC_ITEMS
parseSentences = do 
    xs <- many1 aFormula
    return $ Axiom_items xs

parseClText :: AnnoState.AParser st BASIC_ITEMS
parseClText = do 
     tx <- pModule
     return $ Axiom_items (ps2 (ps tx))

ps :: MODULE -> [SENTENCE]
ps (Mod _ tx _) = senOfText tx
ps (Mod_ex _ _ _ _) = []

ps2 :: [SENTENCE] -> [Annotation.Annoted SENTENCE]
ps2 x = map (\y -> Annotation.Annoted y nullRange [] []) x

senOfText :: TEXT -> [SENTENCE]
senOfText (Text phr _) = foldl (sen2) [] phr
senOfText (Named_text _ t _) = senOfText t

sen2 :: [SENTENCE] -> PHRASE -> [SENTENCE] 
sen2 s p = if (isSen p) then (s ++ [senOfPhr p]) else s

senOfPhr :: PHRASE -> SENTENCE
senOfPhr (Sentence s) = s
senOfPhr _ = Atom_sent (Atom (Name_term (Token "empty" nullRange)) []) nullRange

isSen :: PHRASE -> Bool
isSen (Sentence _) = True
isSen _ = False

-- | parser for Axiom_items
parseAxItems :: AnnoState.AParser st BASIC_ITEMS
parseAxItems = do
       d <- AnnoState.dotT
       (fs, ds) <- aFormula `Lexer.separatedBy` AnnoState.dotT
       (_, an) <- AnnoState.optSemi
       let _  = Id.catRange (d:ds)
           ns = init fs ++ [Annotation.appendAnno (last fs) an]
       return $ Axiom_items ns
       -- return $ Axiom_items [Annotation.Annoted a nullRange [] [] ] 

-- a :: SENTENCE
-- a = Atom_sent (Atom (Name_term (Token "Cube" nullRange)) [Term_seq (Name_term 
--       (Token "a" nullRange))]) nullRange

-- | Toplevel parser for formulae
aFormula :: AnnoState.AParser st (Annotation.Annoted SENTENCE)
aFormula =  do 
     AnnoState.allAnnoParser sentence

-- | collect all the names and sequence markers
symbItems :: GenParser Char st NAME
symbItems = do
  return (Token "x" nullRange)



-----------------------------------------------------------------------------
-- kif parser

parseKif :: AnnoState.AParser st BASIC_ITEMS
parseKif = do 
    ks <- many1 kif
    return $ Axiom_items $ ps2 ks

k :: String
k = ";Comment\n(subclass CodingScheme Procedure);Comment2(Comment Comment)\n(P x);Comment"

-- kif :: CharParser st TEXT
kif :: CharParser st SENTENCE
kif =  do
  skip2 
  s <- sentence
  skip2
  return $ s

test :: IO ()
test = parseTest kif k

eolOrEof :: GenParser Char st ()
eolOrEof = (oneOf "\n\r" >> return ()) <|> eof

commentOut :: CharParser st ()
commentOut = char ';' >> manyTill anyChar eolOrEof >> return ()

skip2 :: CharParser st [()]
skip2 = many ((satisfy isSpace >> return ()) <|> commentOut) -- <|> try docuOut)

lexem :: CharParser st a -> CharParser st a
lexem = (<< skip2)

docuOut :: CharParser st ()
docuOut = parens $ do
     string "documentation"
     white
     scanClWord
     white
     char '"'
     manyTill anyChar (char '"')
     return ()

ds1 :: String
ds1 = "(documentation anyWord \"any documentation ()\")  (formerName \"First World\" DevelopedCountry)"
d2 :: String
d2 = "(formerName \"First World\" DevelopedCountry)\n(conventionalLongName \"Developed Country\" DevelopedCountry)\n(names \"industrial country\" DevelopedCountry)\n(conventionalShortName \"the North\" DevelopedCountry)"
d3 :: String
d3 = "(formerName \"nothing\" DevelopedCountry)"
d4 :: String
d4 = "(holdsDuring (EndFn (WhenFn ?EXPORT)) (not (located ?ITEM ?AREA)))"

parseFileKif :: String -> IO ()
parseFileKif f = do x <- readFile f
                    parseTest (many kif) x

kk :: IO ()
kk = parseFileKif "CommonLogic/TestData/kif.clf"
