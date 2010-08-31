{- |
Module      :  $Header$
Description :  Parser for COL
Copyright   :  (c) Till Mossakowski, Uni Bremen 2004
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

parsing of COL extensions
-}

module COL.Parse_AS where

import Common.AnnoState
import Common.Id
import Common.Lexer
import Common.Token
import COL.AS_COL
import Text.ParserCombinators.Parsec

colSigItems :: AParser st COL_SIG_ITEM
colSigItems =
 do itemList col_reserved_words constructorS parseId Constructor_items
   <|> itemList col_reserved_words observerS observerItem Observer_items

instance AParsable COL_SIG_ITEM where
  aparser = colSigItems

observerItem :: [String] -> AParser st (Id, Maybe Int)
observerItem ks =
    do oParenT
       i <- parseId ks
       anComma
       n <- many1 digit
       cParenT
       return (i, Just $ read n)
