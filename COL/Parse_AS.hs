{-
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

  Parser for modal logic extension of CASL
-}

module COL.Parse_AS where

import Common.AnnoState
import Common.AS_Annotation
import Common.Id
import Common.Keywords
import Common.Lexer
import Common.Token
import COL.AS_COL
import Text.ParserCombinators.Parsec
import CASL.Formula
import CASL.OpItem

colSigItems :: AParser COL_SIG_ITEM
colSigItems = 
 do itemList col_reserved_words constuctorS parseId Constructor_items
   <|> itemList col_reserved_words observerS observerItem Observer_items

instance AParsable COL_SIG_ITEM where
  aparser = rigidSigItems

observerItem :: [String] -> AParser (Id, Maybe Int)
observerItem ks = 
    do oParenT
       id <- parseId ks
       anComma
       n <- many1 digit
       cParenT
       return (id,n)


mKey :: AParser Token
mKey = asKey modalityS <|> asKey modalitiesS

