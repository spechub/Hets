{-
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

  Parser for CASL_DL logic 
-}

module CASL_DL.Parse_AS where

import Common.AnnoState
import Common.AS_Annotation
import Common.Id
import Common.Keywords
import Common.Lexer
import Common.Token

import CASL_DL.AS_CASL_DL

import Text.ParserCombinators.Parsec

import CASL.Formula
import CASL.OpItem

import Data.List

dlFormula :: AParser st DL_FORMULA
dlFormula = 
    do (ct,ctp) <- cardKeyword
       o <- oBracketT
       p <- parseId casl_DL_reserved_words
       c <- cBracketT
       op <- oParenT
       t1 <- term casl_DL_reserved_words 
       co <- anComma 
       t2 <- term casl_DL_reserved_words 
       cp <- cParenT
       return (Cardinality ct p t1 t2 (appRange ctp (concatMapRange tokPos (o:c:op:co:[cp]))))

cardKeyword :: AParser st (CardType,Range)
cardKeyword = 
    do kw <- (asKey cardinalityS <|> 
              asKey minCardinalityS <|> 
              asKey maxCardinalityS)
       return (toCT (tokStr kw),tokPos kw)
    where toCT s 
              | "min" `isPrefixOf` s = CMin
              | "max" `isPrefixOf` s = CMax
              | "car" `isPrefixOf` s = CExact
              | otherwise = error "CASL_DL.Parse_AS.cardKeyword: the impossible happend!!"

instance AParsable DL_FORMULA where
  aparser = dlFormula
