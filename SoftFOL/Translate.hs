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
    ( transId
    , transSenName
    , checkIdentifier
    , CKType (..)
    ) where

import Data.Char
import qualified Data.Set as Set
import qualified Data.Map as Map

import Common.Id
import Common.ProofUtils

import SoftFOL.Sign

data CKType = CKSort | CKVar | CKPred | CKOp

-- | collect all keywords of SoftFOL
reservedWords :: Set.Set String
reservedWords = Set.fromList $ map showSPSymbol
  [ SPEqual
  , SPTrue
  , SPFalse
  , SPOr
  , SPAnd
  , SPNot
  , SPImplies
  , SPImplied
  , SPEquiv]
 -- this list of reserved words has been generated with:
 -- perl HetCATS/utils/transformLexerFile.pl spass-3.0c/dfgscanner.l
  ++ concatMap words
  [ "and author axioms begin_problem by box all clause cnf comp"
  , "conjectures conv date description dia some div dnf domain"
  , "domrestr eml EML DL end_of_list end_problem equal equiv"
  , "exists false forall formula freely functions generated"
  , "hypothesis id implied implies list_of_clauses list_of_declarations"
  , "list_of_descriptions list_of_formulae list_of_general_settings"
  , "list_of_proof list_of_settings list_of_special_formulae"
  , "list_of_symbols list_of_terms logic name not operators"
  , "or prop_formula concept_formula predicate predicates quantifiers"
  , "ranrestr range rel_formula role_formula satisfiable set_DomPred"
  , "set_flag set_precedence set_ClauseFormulaRelation set_selection"
  , "sort sorts status step subsort sum test translpairs true"
  , "unknown unsatisfiable version static"]
  ++ map (('e' :) . show) [0 .. 20 :: Int]
  ++ map (("fmdarwin_e" ++) . show) [0 .. 20 :: Int]

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
-}
-- Warning:
-- Data.Char.isAlphaNum includes all kinds of isolatin1 characters!!
checkSPChar :: Char -> Bool
checkSPChar c = isAlphaNum c && isAscii c || '_' == c

transId :: CKType -> Id -> SPIdentifier
transId t = mkSimpleId . transIdString t . concatMap transToSPChar . show

transIdString :: CKType -> String -> String
transIdString t str = case str of
  "" -> error "SoftFOL.Translate.transId: empty string not allowed"
  c : r -> if isDigit c then transIdString t $ substDigit c ++ r
    else case t of
      CKOp | '_' == c -> 'o' : str
      CKPred | '_' == c -> 'p' : str
      CKVar -> toUpper c : r
      _ -> let lstr = toLower c : r in
        if Set.member lstr reservedWords then "x_" ++ str else lstr

transToSPChar :: Char -> String
transToSPChar c = if checkSPChar c then [c] else
  if elem c " \n" then "_" else
  Map.findWithDefault ("Slash_"++ show (ord c)) c charMap

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
