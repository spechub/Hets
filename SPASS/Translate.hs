{- |
Module      :  $Header$
Description :  Functions used by 'Comorphisms.CASL2SPASS' and 'SPASS.Prove'
               for the translation into valid SPASS identifiers
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  portable

collection of functions used by Comorphisms.CASL2SPASS and SPASS.Prove
 for the translation of CASL identifiers and axiom labels into
 valid SPASS identifiers
-}

module SPASS.Translate (reservedWords, transId, transSenName) where

import Data.Char

import Common.Id
import Common.DocUtils
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Map as Map

import SPASS.Sign
import SPASS.Print ()
import SPASS.Utils

import Common.ProofUtils

-- | collect all keywords of SPASS
reservedWords :: Set.Set SPIdentifier
reservedWords = Set.fromList (map ((flip showDoc) "") [SPEqual
                                          , SPTrue
                                          , SPFalse
                                          , SPOr
                                          , SPAnd
                                          , SPNot
                                          , SPImplies
                                          , SPImplied
                                          , SPEquiv] ++
    words "date name author status description")

transSenName :: String -> String
transSenName = transId CSort . simpleIdToId . mkSimpleId


transId :: CType -> Id -> SPIdentifier
transId t iden
    | checkIdentifier t str =
                            if Set.member str reservedWords
                            then changeFirstChar $ "X_"++str
                            else str
    | otherwise = changeFirstChar $
                  concatMap transToSPChar $
                  addChar str
    where str = changeFirstChar $ substDigits $ show iden
          addChar s =
              case s of
              "" -> error "SPASS.Translate.transId: empty string not allowed"
              ('_':_) -> case t of
                         COp _ -> 'o':s
                         CPred _ -> 'p':s
                         _ -> error $ "SPASS.Translate.transId: Variables "++
                                      "and Sorts don't start with '_'"
              _ -> s
          changeFirstChar s =
              case s of
              "" -> error $ "SPASS.Translate.transId: each identifier "++
                            "must be non empty here"
              (x:xs) -> toValidChar x : xs
          toValidChar =
              case t of
              CVar _ -> toUpper
              _ -> toLower

charMap_SP :: Map.Map Char String
charMap_SP = Map.union
             (Map.fromList [('\'',"Prime")
                           ,(' ',"_")
                           ,('\n',"_")])
             charMap

transToSPChar :: Char -> SPIdentifier
transToSPChar c
    | checkSPChar c = [c]
    | otherwise = Map.findWithDefault def c charMap_SP
    where def = "Slash_"++ show (ord c)

substDigits :: String -> String
substDigits = concatMap subst
    where subst c
              | isDigit c = case c of
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
                _ -> error ("SPASS.Translate.substDigits: unknown digit: \'"
                            ++c:"\'")
              | otherwise = [c]
