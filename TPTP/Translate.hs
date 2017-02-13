{- |
Module      :  ./SoftFOL/Translate.hs
Description :  utility to create valid identifiers for atp provers
Copyright   :  (c) Klaus Luettich, Uni Bremen 2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

collection of functions used by "Comorphisms.SuleCFOL2SoftFOL" and
 "SoftFOL.ProveSPASS" for the translation of CASL identifiers and axiom labels
 into valid SoftFOL identifiers -}

module TPTP.Translate
    ( transId
    , transSenName
    , checkIdentifier
    , CKType (..)
    ) where

import Data.Char
import qualified Data.Set as Set

import Common.Id
import Common.ProofUtils


data CKType = CKSort | CKVar | CKPred | CKOp


transSenName :: String -> String
transSenName = transIdString CKSort . concatMap transToSPChar

{- |
  SPASS Identifiers may contain letters, digits, and underscores only; but
  for TPTP the allowed starting letters are different for each sort of
  identifier.
-}
checkIdentifier :: CKType -> String -> Bool
checkIdentifier t str = case str of
  "" -> False
  c : _ -> all checkSPChar str && case t of
    CKVar -> isUpper c -- for TPTP
    _ -> isLower c

{- |
Allowed SPASS characters are letters, digits, and underscores.
Warning:
Data.Char.isAlphaNum includes all kinds of isolatin1 characters!! -}
checkSPChar :: Char -> Bool
checkSPChar c = isAlphaNum c && isAscii c || '_' == c

transId :: CKType -> Id -> Token
transId t = mkSimpleId . transIdString t . concatMap transToSPChar . show

transIdString :: CKType -> String -> String
transIdString t str = case str of
  "" -> error "SoftFOL.Translate.transId: empty string not allowed"
  c : r -> if isDigit c then transIdString t $ substDigit c ++ r
    else case t of
      CKOp | '_' == c -> 'o' : str
      CKPred | '_' == c -> 'p' : str
      CKVar -> toUpper c : r
      _ -> let lstr = toLower c : r in lstr

transToSPChar :: Char -> String
transToSPChar c
 | checkSPChar c = [c]
 | elem c " \n" = "_"
 | otherwise = lookupCharMap c

substDigit :: Char -> String
substDigit c = case c of
  '0' -> "zero"
  '1' -> "one"
  '2' -> "two"
  '3' -> "three"
  '4' -> "four"
  '5' -> "five"
  '6' -> "six"
  '7' -> "seven"
  '8' -> "eight"
  '9' -> "nine"
  _ -> [c]
