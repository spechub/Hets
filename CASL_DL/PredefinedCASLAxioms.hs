{- |
Module      :  PredefinedSign.hs
Description :  with inlined axioms
Copyright   :  (c) Uni and DFKI Bremen 2005-2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module CASL_DL.PredefinedCASLAxioms
  ( predefSign
  , thing
  , noThing
  , predefinedAxioms
  ) where

import CASL.AS_Basic_CASL
import CASL.Sign

import Common.AS_Annotation
import Common.Id
import Common.Lib.Rel as Rel
import qualified Common.Lib.MapSet as MapSet

import Data.Char
import Data.Set as Set

hetsPrefix :: String
hetsPrefix = ""

-- | OWL topsort Thing
thing :: SORT
thing = stringToId "Thing"

n :: Range
n = nullRange

-- | OWL bottom
noThing :: PRED_SYMB
noThing =
     (Qual_pred_name (stringToId "Nothing")
                         (Pred_type [thing] n) n)

predefSign :: Sign () ()
predefSign
  = (emptySign ()){sortSet =
                     Set.fromList
                       [Id [Token "Char" n] [] n,
                        Id [Token "DATA" n] [] n,
                        Id [Token "boolean" n] [] n,
                        Id [Token "integer" n] [] n,
                        Id [Token "negativeInteger" n] [] n,
                        Id [Token "nonNegativeInteger" n] [] n,
                        Id [Token "nonPositiveInteger" n] [] n,
                        Id [Token "positiveInteger" n] [] n,
                        Id [Token "string" n] [] n],
                   sortRel =
                     Rel.fromList
                       [(Id [Token "boolean" n] [] n,
                         Id [Token "DATA" n] [] n),
                        (Id [Token "integer" n] [] n,
                         Id [Token "DATA" n] [] n),
                        (Id [Token "negativeInteger" n] [] n,
                         Id [Token "DATA" n] [] n),
                        (Id [Token "negativeInteger" n] [] n,
                         Id [Token "integer" n] [] n),
                        (Id [Token "negativeInteger" n] [] n,
                         Id [Token "nonPositiveInteger" n] [] n),
                        (Id [Token "nonNegativeInteger" n] [] n,
                         Id [Token "DATA" n] [] n),
                        (Id [Token "nonNegativeInteger" n] [] n,
                         Id [Token "integer" n] [] n),
                        (Id [Token "nonPositiveInteger" n] [] n,
                         Id [Token "DATA" n] [] n),
                        (Id [Token "nonPositiveInteger" n] [] n,
                         Id [Token "integer" n] [] n),
                        (Id [Token "positiveInteger" n] [] n,
                         Id [Token "DATA" n] [] n),
                        (Id [Token "positiveInteger" n] [] n,
                         Id [Token "integer" n] [] n),
                        (Id [Token "positiveInteger" n] [] n,
                         Id [Token "nonNegativeInteger" n] [] n),
                        (Id [Token "positiveInteger" n] [] n,
                         Id [Token "DATA" n] [] n),
                        (Id [Token "positiveInteger" n] [] n,
                         Id [Token "integer" n] [] n),
                        (Id [Token "positiveInteger" n] [] n,
                         Id [Token "nonNegativeInteger" n] [] n),
                        (Id [Token "string" n] [] n,
                         Id [Token "DATA" n] [] n)],
                   predMap =
                     MapSet.fromList
                       [(Id [Token "Nothing" n] [] n,
                           [PredType [Id [Token "Thing" n] [] n]]),
                        (Id
                           [Token "__" n, Token "<" n, Token "__" n]
                           []
                           n,
                           [PredType
                              [Id [Token "integer" n] [] n,
                               Id [Token "integer" n] [] n],
                            PredType
                              [Id [Token "nonNegativeInteger" n] [] n,
                               Id [Token "nonNegativeInteger" n] [] n]]),
                        (Id
                           [Token "__" n, Token "<=" n, Token "__" n]
                           []
                           n,
                           [PredType
                              [Id [Token "integer" n] [] n,
                               Id [Token "integer" n] [] n],
                            PredType
                              [Id [Token "nonNegativeInteger" n] [] n,
                               Id [Token "nonNegativeInteger" n] [] n]]),
                        (Id
                           [Token "__" n, Token ">" n, Token "__" n]
                           []
                           n,
                           [PredType
                              [Id [Token "integer" n] [] n,
                               Id [Token "integer" n] [] n],
                            PredType
                              [Id [Token "nonNegativeInteger" n] [] n,
                               Id [Token "nonNegativeInteger" n] [] n]]),
                        (Id
                           [Token "__" n, Token ">=" n, Token "__" n]
                           []
                           n,
                           [PredType
                              [Id [Token "integer" n] [] n,
                               Id [Token "integer" n] [] n],
                            PredType
                              [Id [Token "nonNegativeInteger" n] [] n,
                               Id [Token "nonNegativeInteger" n] [] n]]),
                        (Id [Token "even" n] [] n,
                           [PredType [Id [Token "integer" n] [] n],
                            PredType
                              [Id [Token "nonNegativeInteger" n] [] n]]),
                        (Id [Token "odd" n] [] n,
                           [PredType [Id [Token "integer" n] [] n],
                            PredType
                              [Id [Token "nonNegativeInteger" n] [] n]])]}

predefinedAxioms :: [SenAttr (FORMULA ()) [Char]]
predefinedAxioms =
    [
     makeNamed "nothing in Nothing" $
     Quantification Universal
     [Var_decl [mk_Name 1] thing n]
     (
      Negation
      (
       Predication
       noThing
       [Qual_var (mk_Name 1) thing n]
       n
      )
      n
     )
     n
    ,
     makeNamed "thing in Thing" $
     Quantification Universal
     [Var_decl [mk_Name 1] thing n]
     (
       Predication
       (Qual_pred_name (stringToId "Thing")
                           (Pred_type [thing] n) n)
       [Qual_var (mk_Name 1) thing n]
       n
     )
     n
    ]

-- | Build a name
mk_Name :: Int -> Token
mk_Name i = mkSimpleId $ hetsPrefix ++  mk_Name_H i
    where
      mk_Name_H k =
          case k of
            0 -> ""
            j ->  (mk_Name_H (j `div` 26)) ++ [(chr ((j `mod` 26) + 96))]
