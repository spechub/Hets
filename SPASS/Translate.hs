{- |
Module      :  $Header$
Description :  Functions used by 'Comorphisms.CASL2SPASS' and 'SPASS.Prove' for the translation into valid SPASS identifiers
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  portable

 collection of functions used by Comorphisms.CASL2SPASS and SPASS.Prove
 for the translation of CASL identifiers and axiom labels into
 valid SPASS identifiers 
-}

module SPASS.Translate where 

import Data.Char

import Common.Id
import Common.PrettyPrint
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Map as Map

import SPASS.Sign
import SPASS.Print ()

import Common.ProofUtils

-- | collect all keywords of SPASS
reservedWords :: Set.Set SPIdentifier 
reservedWords = Set.fromList (map ((flip showPretty) "") [SPEqual
                                          , SPTrue 
                                          , SPFalse 
                                          , SPOr 
                                          , SPAnd
                                          , SPNot
                                          , SPImplies
                                          , SPImplied
                                          ,SPEquiv])

transSenName :: String -> String
transSenName = transId . simpleIdToId . mkSimpleId

transId :: Id -> SPIdentifier
transId iden 
    | checkIdentifier str = substDigits $
                            if Set.member str reservedWords 
                            then "X_"++str
                            else str
    | otherwise = substDigits $ concatMap transToSPChar (dropWhile (=='_') str)
    where str = show iden

charMap_SP :: Map.Map Char String
charMap_SP = Map.union charMap 
             (Map.fromList [('\'',"Prime")
                           ,(' ',"_")])

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
