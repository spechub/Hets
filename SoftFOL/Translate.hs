{- |
Module      :  $Header$
Description :  utility to create valid identifiers for atp provers
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

collection of functions used by "Comorphisms.SuleCFOL2SoftFOL" and
 "SoftFOL.ProveSPASS" for the translation of CASL identifiers and axiom labels
 into valid SoftFOL identifiers -}

module SoftFOL.Translate
    ( reservedWords
    , transId
    , transSenName
    , checkIdentifier
    , CKType (..)
    ) where

import Data.Char

import Common.Id
import Common.DocUtils
import qualified Data.Set as Set
import qualified Data.Map as Map

import SoftFOL.Sign
import SoftFOL.Print ()

import Common.ProofUtils

data CKType = CKSort | CKVar | CKPred | CKOp

-- | collect all keywords of SoftFOL
reservedWords :: Set.Set SPIdentifier
reservedWords = Set.fromList $ map (mkSimpleId . (flip showDoc) "") [SPEqual
                                          , SPTrue
                                          , SPFalse
                                          , SPOr
                                          , SPAnd
                                          , SPNot
                                          , SPImplies
                                          , SPImplied
                                          , SPEquiv] ++
 -- this list of reserved words has been generated with:
 -- perl HetCATS/utils/transformLexerFile.pl spass-3.0c/dfgscanner.l
   map mkSimpleId (words
    $ "and author axioms begin_problem by box all clause cnf comp "++
      "conjectures conv date description dia some div dnf domain "++
      "domrestr eml EML DL end_of_list end_problem equal equiv "++
      "exists false forall formula freely functions generated "++
      "hypothesis id implied implies list_of_clauses list_of_declarations "++
      "list_of_descriptions list_of_formulae list_of_general_settings "++
      "list_of_proof list_of_settings list_of_special_formulae "++
      "list_of_symbols list_of_terms logic name not operators "++
      "or prop_formula concept_formula predicate predicates quantifiers "++
      "ranrestr range rel_formula role_formula satisfiable set_DomPred "++
      "set_flag set_precedence set_ClauseFormulaRelation set_selection "++
      "sort sorts status step subsort sum test translpairs true "++
      "unknown unsatisfiable version static"
     ) ++ map (mkSimpleId . ('e' :) . show) [1 .. 20 :: Int]

transSenName :: String -> String
transSenName = show . transId CKSort . simpleIdToId . mkSimpleId


{- |
  SPASS Identifiers may contain letters, digits, and underscores only; but
  for TPTP the allowed starting letters are different for each sort of
  identifier.
-}
checkIdentifier :: CKType -> String -> Bool
checkIdentifier _ "" = False
checkIdentifier t xs@(x:_) = and ((checkFirstChar t x) : map checkSPChar xs)

{- |
Allowed SPASS characters are letters, digits, and underscores.
-}
-- Warning:
-- Data.Char.isAlphaNum includes all kinds of isolatin1 characters!!
checkSPChar :: Char -> Bool
checkSPChar c = (isAlphaNum c && isAscii c )|| '_' == c

{- |
  important for TPTP format
-}
checkFirstChar :: CKType -> Char -> Bool
checkFirstChar t = case t of
                     CKVar -> isUpper
                     _ -> isLower

transId :: CKType -> Id -> SPIdentifier
transId t iden
    | checkIdentifier t str = mkSimpleId
        $ if Set.member (mkSimpleId str) reservedWords
          then changeFirstChar $ "X_"++str
          else str
    | otherwise = mkSimpleId $ changeFirstChar $
                  concatMap transToSPChar $
                  addChar str
    where str = changeFirstChar $ show iden
          addChar s =
              case s of
              "" -> error "SoftFOL.Translate.transId: empty string not allowed"
              ('_':_) -> case t of
                         CKOp -> 'o':s
                         CKPred -> 'p':s
                         _ -> error $ "SoftFOL.Translate.transId: Variables "++
                                      "and Sorts don't start with '_'"
              _ -> s
          changeFirstChar s =
              case s of
              "" -> error $ "SoftFOL.Translate.transId: each identifier "++
                            "must be non empty here"
              (x:xs) -> if isDigit x
                 then changeFirstChar $ substDigits [x] ++ xs
                 else toValidChar x : xs
          toValidChar =
              case t of
              CKVar -> toUpper
              _ -> toLower

charMap_SP :: Map.Map Char String
charMap_SP = foldr (\ k -> Map.insert k "_") charMap " \n"

transToSPChar :: Char -> String
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
                _ -> error ("SoftFOL.Translate.substDigits: unknown digit: \'"
                            ++c:"\'")
              | otherwise = [c]
