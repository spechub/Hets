{- |
Module      :  ./OWL2/Translate.hs
Description :  translate string to OWL2 valid names
Copyright   :  (c) C. Maeder, DFKI GmbH 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable
-}

module OWL2.Translate where

import Common.Id
import Common.ProofUtils

import Data.Char

import OWL2.AS
import OWL2.Parse

idToIRI :: Id -> QName
idToIRI = idToAnonIRI False

idToAnonIRI :: Bool -> Id -> QName
idToAnonIRI = idToAnonNumberedIRI (-1)

idToNumberedIRI :: Id -> Int -> QName
idToNumberedIRI i n = idToAnonNumberedIRI n False i

idToAnonNumberedIRI :: Int -> Bool -> Id -> QName
idToAnonNumberedIRI n b i = nullQName
  { localPart = (if b then ('_' :) else id) $ transString (show i)
      ++ if n < 0 then "" else '_' : show n
  , iriPos = rangeOfId i }

-- | translate to a valid OWL string
transString :: String -> String
transString str = let
    x = 'x'
    replaceChar1 d | d == x = [x, x]  -- code out existing x!
                   | iunreserved d = [d]
                   | otherwise = x : replaceChar d
    in case str of
    "" -> [x]
    c : s -> let l = replaceChar1 c in
             (if isDigit c || c == '_' then [x, c]
             else l) ++ concatMap replaceChar1 s

-- | injective replacement of special characters
replaceChar :: Char -> String
-- <http://www.htmlhelp.com/reference/charset/>
replaceChar c = if isAlphaNum c then [c] else lookupCharMap c
