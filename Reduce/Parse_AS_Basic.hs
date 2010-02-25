{- |
Module      :  $Header$
Description :  Parser for basic specs
Copyright   :  (c) Dominik Dietrich, Uni Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  dominik.dietrich@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Parser for abstract syntax for reduce computer algebra system
-}

module Reduce.Parse_AS_Basic
    where

import qualified Common.AnnoState as AnnoState
import qualified Common.AS_Annotation as Annotation
import Common.Id as Id
import Common.Keywords as Keywords
import Common.Lexer as Lexer
import Control.Monad

import Reduce.AS_BASIC_Reduce
import Reduce.Keywords
import Text.ParserCombinators.Parsec

-- the basic lexer, test using e.g. runParser identifier 0 "" "asda2_3"

-- | parsing of identifiers. an identifier is a letter followed by letters/numbers/_, but not a keyword
identifier :: CharParser st Id.Token
identifier = Lexer.pToken $ Lexer.reserved allKeywords Lexer.scanAnyWords

-- | parser for numbers (both integers and floats) without signs
number :: CharParser st Id.Token
number = Lexer.pToken Lexer.scanFloat

expression :: CharParser st EXPRESSION
expression = do
  exp1 <- factor
  exps <- many $ liftM2 (,) (Lexer.keySign (string "+" <|> string "-")) factor
  if null exps then return exp1  
     else return $ foldr (\ a b -> (Op (fst a) [b,(snd a)] nullRange)) exp1 exps

-- | parse a product of basic expressions
factor :: CharParser st EXPRESSION
factor = do
  exp1 <- expexp 
  exps <- many $ liftM2 (,) (Lexer.keySign (string "*" <|> string "/")) factor
  if null exps then return exp1  
     else return $ foldr (\ a b -> (Op (fst a) [b,(snd a)] nullRange)) exp1 exps

-- | parse a sequence of exponentiations
expexp :: CharParser st EXPRESSION
expexp = do
  exp1 <- expatom 
  exps <- many $ liftM2 (,) (Lexer.keySign (string "**" <|> string "^")) expexp
  if null exps then return exp1  
    else return $ foldr (\ a b -> (Op (fst a) [b,(snd a)] nullRange)) exp1 exps
  
         
-- | parse a basic expression
expatom :: CharParser st EXPRESSION
expatom = do
  nr <- number
  return (Double 2 Id.nullRange)
  <|> 
  do
    id <- identifier
    return (Var id)
  <|>
  do
    oParenT
    exp <- expression
    cParenT
    return exp

-- test cases
-- runParser expression 2 "" "x+y+y"
 

