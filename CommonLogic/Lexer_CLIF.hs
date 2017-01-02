{- |
Module      :  ./CommonLogic/Lexer_CLIF.hs
Description :  Parser of common logic interchange format
Copyright   :  (c) Karl Luc, DFKI Bremen 2010
License     :  GPLv2 or higher

Maintainer  :  kluc@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Parser of common logic interchange format
-}

-- Ref. Common Logic ISO/IEC IS 24707:2007(E)

module CommonLogic.Lexer_CLIF where

import CommonLogic.AS_CommonLogic
import Common.Id as Id
import qualified Common.Lexer as Lexer
import Common.Lexer (parens)
import Common.Parsec
import Common.Keywords

import Text.ParserCombinators.Parsec as Parsec
import Data.Char (ord)

pToken :: CharParser st String -> CharParser st Token
pToken p = Lexer.pToken p << many white

oParenT :: CharParser st Token
oParenT = Lexer.oParenT << many white

cParenT :: CharParser st Token
cParenT = Lexer.cParenT << many white

quotedstring :: CharParser st String
quotedstring = do
   c1 <- char '\''
   s <- many (satisfy clLetters2 <|> oneOf (whitec ++ "()\""))
        <?> "quotedstring: word"
   c2 <- char '\''
   many white
   return $ c1 : s ++ [c2]

enclosedname :: CharParser st String
enclosedname = do
   c1 <- char '\"'
   s <- many (satisfy clLetters2 <|> oneOf (whitec ++ "@()'"))
         <?> "word"
   c2 <- char '\"' <?> "\""
   many white
   return $ c1 : s ++ [c2]

-- Parser Keywords
andKey :: CharParser st Id.Token
andKey = pToken (string andS) <?> "conjunction"

notKey :: CharParser st Id.Token
notKey = pToken (string notS) <?> "negation"

orKey :: CharParser st Id.Token
orKey = pToken (string orS) <?> "disjunction"

ifKey :: CharParser st Id.Token
ifKey = pToken (string ifS) <?> "implication"

iffKey :: CharParser st Id.Token
iffKey = pToken (string iffS) <?> "equivalence"

forallKey :: CharParser st Id.Token
forallKey = pToken (string forallS) <?> "universal quantification"

existsKey :: CharParser st Id.Token
existsKey = pToken (string existsS) <?> "existential quantification"

thatKey :: CharParser st Id.Token
thatKey = pToken (string "that") <?> "\"that\" term"

-- cl keys
clTextKey :: CharParser st Id.Token
clTextKey = pToken (try (string "cl-text") <|> string "cl:text") <?> "text"

clModuleKey :: CharParser st Id.Token
clModuleKey = pToken (try (string "cl-module") <|> string "cl:module")
              <?> "module"

clImportsKey :: CharParser st Id.Token
clImportsKey = pToken (try (string "cl-imports") <|> string "cl:imports")
               <?> "importation"

clExcludesKey :: CharParser st Id.Token
clExcludesKey = pToken (try (string "cl-excludes") <|> string "cl:excludes")
                <?> "exclusion list"

clEqualsKey :: CharParser st Id.Token
clEqualsKey = pToken (string "=") <?> "equation"

clCommentKey :: CharParser st Id.Token
clCommentKey = pToken (try (string "cl-comment") <|> string "cl:comment")
               <?> "comment"

clRolesetKey :: CharParser st Id.Token
clRolesetKey = pToken (string "cl-roleset" <|> string "roleset:") <?> "roleset"

clPrefixKey :: CharParser st Id.Token
clPrefixKey = pToken (string "cl-prefix") <?> "prefix"

seqmark :: CharParser st Id.Token
seqmark = pToken (reserved reservedelement2 scanSeqMark) <?> "sequence marker"

identifier :: CharParser st Id.Token
identifier = pToken (reserved reservedelement scanClWord) <?> "name"

scanSeqMark :: CharParser st String
scanSeqMark = do
           sq <- string "..."
           w <- many clLetter <?> "sequence marker"
           return $ sq ++ w

scanClWord :: CharParser st String
scanClWord = quotedstring <|> enclosedname <|> (many1 clLetter <?> "words")

clLetters :: Char -> Bool
clLetters ch = let c = ord ch in
   c >= 33 && c <= 126 && (c <= 38 && c /= 34
      || c >= 42 && c /= 64 && c /= 92)

clLetters2 :: Char -> Bool
clLetters2 ch = let c = ord ch in
   (c >= 32 && c <= 126 && (c <= 38 && c /= 34
      || c >= 42 && c /= 64)) || c >= 128

-- a..z, A..z, 0..9, ~!#$%^&*_+{}|:<>?`-=[];,.

clLetter :: CharParser st Char
clLetter = satisfy clLetters <?> "cl letter"

reservedelement :: [String]
reservedelement = ["=", "and", "or", "iff", "if", "forall", "exists", "not"
                  , "that", "...", "cl:text", "cl:imports", "cl:excludes"
                  , "cl:module", "cl:comment", "roleset:"] ++ reservedcl

reservedcl :: [String]
reservedcl = ["cl-text", "cl-imports", "cl-excludes", "cl-module"
             , "cl-comment", "cl-roleset"]

-- reserved elements for sequence marker
reservedelement2 :: [String]
reservedelement2 = ["=", "and", "or", "iff", "if", "forall", "exists", "not"
                   , "that", "cl:text", "cl:imports", "cl:excludes", "cl:module"
                   , "cl:comment", "roleset:"]

commentBlockOpen :: String
commentBlockOpen = "/*"

commentBlockClose :: String
commentBlockClose = "*/"

commentLineStart :: String
commentLineStart = "//"

newLinec :: String
newLinec = "\n\r"

whitec :: String
whitec = newLinec ++ "\t\v\f "

whiteSpace :: CharParser st String
whiteSpace = many1 $ oneOf whitec

commentBlock :: CharParser st String
commentBlock =
  string commentBlockOpen >> manyTill anyChar (try $ string commentBlockClose)
  <?> ""

commentLine :: CharParser st String
commentLine =
  string commentLineStart >> many (noneOf newLinec) <?> ""

white :: CharParser st String
white =
    whiteSpace
  <|>
    try commentLine
  <|>
    commentBlock
