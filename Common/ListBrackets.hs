
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  All rights reserved.

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable
    
parse b1__b2 in %list-annotations differently from mixIds. 

An opening square bracket in b1 must not be interpreted as the beginning of
a compound list. b1 and b2 must not contain places. b1 must at least
have one open brace or square bracket to ensure that list
elements can be comma separated. b2 may end with a
compound-list. Braces and brackets in b1__b2 together must match.

-}

module Common.ListBrackets where

import Common.Token
import Common.Id (Id(Id), Token(..), isPlace)
import Common.Lib.Parsec

checkForPlaces :: ([String], [String]) -> [Token] -> GenParser Char st [Token] 
checkForPlaces l ts = 
    do let ps = filter isPlace ts
       if length ps == 0 then nextListToks topMix3 l 
	  -- topMix3 starts with square brackets 
	  else if length ps > 1 then unexpected "multiple places"
	       else return []

nextListToks :: (([String], [String]) -> GenParser Char st [Token])
	     -> ([String], [String]) -> GenParser Char st [Token]
nextListToks f l = 
    do ts <- f l 
       cs <- checkForPlaces l ts
       return (ts ++ cs)

listBrackets :: ([String], [String]) -> ([String], [String]) 
	     -> GenParser Char st Id
listBrackets keys idKeys = 
    do l <- nextListToks afterPlace keys -- start somehow
       (c, p) <- option ([], []) (comps idKeys)
       return (Id l c p)

caslListBrackets :: GenParser Char st Id
caslListBrackets = listBrackets casl_keys casl_keys
