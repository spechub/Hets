{- |
Module      :  $Header$
Description :  Parser of common logic interface format
Copyright   :  (c) Karl Luc, DFKI Bremen 2010
License     :  GPLv2 or higher

Maintainer  :  kluc@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Parser of common logic interface format
-}

{-
  Ref. Common Logic ISO/IEC IS 24707:2007(E)
-}

module CommonLogic.Lexer_CLIF where

import qualified Common.AnnoState as AnnoState
import qualified Common.AS_Annotation as Annotation
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
quotedstring = do
   char '\''
   s <- (many $ (satisfy clLetters2) <|> (oneOf whitec)
         <|> char '(' <|> char ')' <|> char '\"')
        <?> "quotedstring: word"
   char '\''
   return $ s

enclosedname :: CharParser st String
enclosedname = do
   char '\"'
   s <- (many $ (satisfy clLetters2) <|> (oneOf whitec)
         <|> char '(' <|> char ')' <|> char '\'')
         <?> "word"
   char '\"' <?> "\""
   return s

-- | parser for parens
parens :: CharParser st a -> CharParser st a
parens p = do
   spaces
   oParenT >> p << cParenT

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

-- Parser Keywords
andKey :: CharParser st Id.Token
andKey = Lexer.pToken $ string andS

notKey :: CharParser st Id.Token
notKey = Lexer.pToken $ string notS

orKey :: CharParser st Id.Token
orKey = Lexer.pToken $ string orS

ifKey :: CharParser st Id.Token
ifKey = (Lexer.pToken $ string ifS)

iffKey :: CharParser st Id.Token
iffKey = (Lexer.pToken $ string iffS)

forallKey :: CharParser st Id.Token
forallKey = Lexer.pToken $ string forallS

existsKey :: CharParser st Id.Token
existsKey = Lexer.pToken $ string existsS

-- cl :: CharParser st a -> CharParser st a
-- cl p = string "cl-" >> p

-- cl keys
clTextKey :: CharParser st Id.Token
clTextKey = Lexer.pToken $ string "cl-text"

clModuleKey :: CharParser st Id.Token
clModuleKey = Lexer.pToken $ string "cl-module"

clImportsKey :: CharParser st Id.Token
clImportsKey = Lexer.pToken $ string "cl-imports"

clExcludesKey :: CharParser st Id.Token
clExcludesKey = Lexer.pToken $ string "cl-excludes"

clCommentKey :: CharParser st Id.Token
clCommentKey = Lexer.pToken $ string "cl-comment"

seqmark :: CharParser st Id.Token
seqmark = Lexer.pToken $ reserved reservedelement2 $ scanSeqMark

identifier :: CharParser st Id.Token
identifier = Lexer.pToken $ reserved reservedelement $ scanClWord

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
reservedcl = ["cl-text", "cl-imports", "cl-exlcudes", "cl-module"
             , "cl-comment"]

-- reserved elements for sequence marker
reservedelement2 :: [String]
reservedelement2 = ["=", "and", "or", "iff", "if", "forall", "exists", "not"
                   , "cl:text", "cl:imports", "cl:excludes", "cl:module"
                   , "cl:comment", "roleset:"]

whitec :: String
whitec = "\n\r\t\v\f "

white :: CharParser st String
white = many1 $ oneOf whitec
