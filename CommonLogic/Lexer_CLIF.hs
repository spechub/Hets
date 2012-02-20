{- |
Module      :  $Header$
Description :  Parser of common logic interchange format
Copyright   :  (c) Karl Luc, DFKI Bremen 2010
License     :  GPLv2 or higher

Maintainer  :  kluc@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Parser of common logic interchange format
-}

{-
  Ref. Common Logic ISO/IEC IS 24707:2007(E)
-}

module CommonLogic.Lexer_CLIF where

import CommonLogic.AS_CommonLogic
import Common.Id as Id
import Common.Lexer as Lexer
import Common.Parsec
import Common.Keywords

import Text.ParserCombinators.Parsec as Parsec
import Data.Char (ord)

name :: CharParser st String
name = do
        x <- identifier
        return $ (tokStr x)

quotedstring :: CharParser st String
quotedstring = many white >> do
   char '\''
   s <- (many $ (satisfy clLetters2) <|> oneOf whitec
         <|> char '(' <|> char ')' <|> char '\"')
        <?> "quotedstring: word"
   char '\''
   return $ s

enclosedname :: CharParser st String
enclosedname = many white >> do
   char '\"'
   s <- (many $ (satisfy clLetters2) <|> oneOf whitec
         <|> char '(' <|> char ')' <|> char '\'')
         <?> "word"
   char '\"' <?> "\""
   return s

-- | parser for parens
parens :: CharParser st a -> CharParser st a
parens p = do
   many white
   oParenT >> many white >> p << many white << cParenT

{-
-- | parser for ignoring parentheses
-- why do i need that?
par :: CharParser st a -> CharParser st a
par p = do
    try oParenT
    x <- p
    cParenT
    return x
  <|> do
    x <- p
    return x
-}

-- Parser Keywords
andKey :: CharParser st Id.Token
andKey = do
  many white
  Lexer.pToken $ string andS

notKey :: CharParser st Id.Token
notKey = do
  many white
  Lexer.pToken $ string notS

orKey :: CharParser st Id.Token
orKey = do
  many white
  Lexer.pToken $ string orS

ifKey :: CharParser st Id.Token
ifKey = do
  many white
  Lexer.pToken $ string ifS

iffKey :: CharParser st Id.Token
iffKey = do
  many white
  Lexer.pToken $ string iffS

forallKey :: CharParser st Id.Token
forallKey = do
  many white
  Lexer.pToken $ string forallS

existsKey :: CharParser st Id.Token
existsKey = do
  many white
  Lexer.pToken $ string existsS

-- cl :: CharParser st a -> CharParser st a
-- cl p = string "cl-" >> p

-- cl keys
clTextKey :: CharParser st Id.Token
clTextKey = do
  many white
  Lexer.pToken $ try (string "cl-text") <|> string "cl:text"

clModuleKey :: CharParser st Id.Token
clModuleKey = do
  many white
  Lexer.pToken $ try (string "cl-module") <|> string "cl:module"

clImportsKey :: CharParser st Id.Token
clImportsKey = do
  many white
  Lexer.pToken $ try (string "cl-imports") <|> string "cl:imports"

clExcludesKey :: CharParser st Id.Token
clExcludesKey = do
  many white
  Lexer.pToken $ try (string "cl-excludes") <|> string "cl:excludes"

clCommentKey :: CharParser st Id.Token
clCommentKey = do
  many white
  Lexer.pToken $ try (string "cl-comment") <|> string "cl:comment"

clRolesetKey :: CharParser st Id.Token
clRolesetKey = do
  many white
  Lexer.pToken $ string "cl-roleset" <|> string "roleset:"

seqmark :: CharParser st Id.Token
seqmark = do
  many white
  Lexer.pToken $ reserved reservedelement2 $ scanSeqMark

identifier :: CharParser st Id.Token
identifier = do
  many white
  Lexer.pToken $ reserved reservedelement $ scanClWord

scanSeqMark :: CharParser st String
scanSeqMark = do
           sq <- string "..."
           w <- many clLetter <?> "sequence marker"
           return $ sq ++ w

scanClWord :: CharParser st String
scanClWord = quotedstring <|> enclosedname <|> (many1 clLetter <?> "words")

clLetters :: Char -> Bool
clLetters ch = let c = ord ch in
   if c >= 33 && c <= 126 then c <= 38 && c /= 34
      || c >= 42 && c /= 64 && c /= 92
   else False

clLetters2 :: Char -> Bool
clLetters2 ch = let c = ord ch in
   if c >= 32 && c <= 126 then c <= 38 && c /= 34
      || c >= 42 && c /= 64 && c /= 92
   else False

-- a..z, A..z, 0..9, ~!#$%^&*_+{}|:<>?`-=[];,.

clLetter :: CharParser st Char
clLetter = satisfy clLetters <?> "cl letter"

reservedelement :: [String]
reservedelement = ["=", "and", "or", "iff", "if", "forall", "exists", "not"
                  , "...", "cl:text", "cl:imports", "cl:excludes", "cl:module"
                  , "cl:comment", "roleset:"] ++ reservedcl

reservedcl :: [String]
reservedcl = ["cl-text", "cl-imports", "cl-excludes", "cl-module"
             , "cl-comment", "cl-roleset"]

-- reserved elements for sequence marker
reservedelement2 :: [String]
reservedelement2 = ["=", "and", "or", "iff", "if", "forall", "exists", "not"
                   , "cl:text", "cl:imports", "cl:excludes", "cl:module"
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

commentLine :: CharParser st String
commentLine =
  string commentLineStart >> manyTill anyChar (try $ oneOf newLinec)

white :: CharParser st String
white =
    whiteSpace
  <|>
    try commentLine
  <|>
    commentBlock
