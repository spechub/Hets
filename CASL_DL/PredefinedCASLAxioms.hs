{- |
Module      :  PredefinedSign.hs
Description :  with inlined axioms
Copyright   :  (c) Uni and DFKI Bremen 2005-2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module CASL_DL.PredefinedCASLAxioms where

import Common.Id
import CASL.AS_Basic_CASL
import Common.AS_Annotation
import CASL.Sign
import Data.Set as Set
import Data.Map as Map
import Common.Lib.Rel as Rel
import Data.Char

hetsPrefix :: String
hetsPrefix = ""

-- | OWL topsort Thing
thing :: SORT
thing = stringToId "Thing"

-- | OWL bottom
noThing :: PRED_SYMB
noThing =
     (Qual_pred_name (stringToId "Nothing")
                         (Pred_type [thing] nullRange) nullRange)

predefSign :: Sign () ()
predefSign
  = (emptySign ()){sortSet =
                     Set.fromList
                       [Id [Token "Char" nullRange] [] nullRange,
                        Id [Token "DATA" nullRange] [] nullRange,
                        Id [Token "boolean" nullRange] [] nullRange,
                        Id [Token "integer" nullRange] [] nullRange,
                        Id [Token "negativeInteger" nullRange] [] nullRange,
                        Id [Token "nonNegativeInteger" nullRange] [] nullRange,
                        Id [Token "nonPositiveInteger" nullRange] [] nullRange,
                        Id [Token "positiveInteger" nullRange] [] nullRange,
                        Id [Token "string" nullRange] [] nullRange],
                   sortRel =
                     Rel.fromList
                       [(Id [Token "boolean" nullRange] [] nullRange,
                         Id [Token "DATA" nullRange] [] nullRange),
                        (Id [Token "integer" nullRange] [] nullRange,
                         Id [Token "DATA" nullRange] [] nullRange),
                        (Id [Token "negativeInteger" nullRange] [] nullRange,
                         Id [Token "DATA" nullRange] [] nullRange),
                        (Id [Token "negativeInteger" nullRange] [] nullRange,
                         Id [Token "integer" nullRange] [] nullRange),
                        (Id [Token "negativeInteger" nullRange] [] nullRange,
                         Id [Token "nonPositiveInteger" nullRange] [] nullRange),
                        (Id [Token "nonNegativeInteger" nullRange] [] nullRange,
                         Id [Token "DATA" nullRange] [] nullRange),
                        (Id [Token "nonNegativeInteger" nullRange] [] nullRange,
                         Id [Token "integer" nullRange] [] nullRange),
                        (Id [Token "nonPositiveInteger" nullRange] [] nullRange,
                         Id [Token "DATA" nullRange] [] nullRange),
                        (Id [Token "nonPositiveInteger" nullRange] [] nullRange,
                         Id [Token "integer" nullRange] [] nullRange),
                        (Id [Token "positiveInteger" nullRange] [] nullRange,
                         Id [Token "DATA" nullRange] [] nullRange),
                        (Id [Token "positiveInteger" nullRange] [] nullRange,
                         Id [Token "integer" nullRange] [] nullRange),
                        (Id [Token "positiveInteger" nullRange] [] nullRange,
                         Id [Token "nonNegativeInteger" nullRange] [] nullRange),
                        (Id [Token "positiveInteger" nullRange] [] nullRange,
                         Id [Token "DATA" nullRange] [] nullRange),
                        (Id [Token "positiveInteger" nullRange] [] nullRange,
                         Id [Token "integer" nullRange] [] nullRange),
                        (Id [Token "positiveInteger" nullRange] [] nullRange,
                         Id [Token "nonNegativeInteger" nullRange] [] nullRange),
                        (Id [Token "string" nullRange] [] nullRange,
                         Id [Token "DATA" nullRange] [] nullRange)],
                   opMap =
                     Map.fromList [],
                   assocOps = Map.fromList [],
                   predMap =
                     Map.fromList
                       [(Id [Token "Nothing" nullRange] [] nullRange,
                         Set.fromList
                           [PredType [Id [Token "Thing" nullRange] [] nullRange]]),
                        (Id
                           [Token "__" nullRange, Token "<" nullRange, Token "__" nullRange]
                           []
                           nullRange,
                         Set.fromList
                           [PredType
                              [Id [Token "integer" nullRange] [] nullRange,
                               Id [Token "integer" nullRange] [] nullRange],
                            PredType
                              [Id [Token "nonNegativeInteger" nullRange] [] nullRange,
                               Id [Token "nonNegativeInteger" nullRange] [] nullRange]]),
                        (Id
                           [Token "__" nullRange, Token "<=" nullRange, Token "__" nullRange]
                           []
                           nullRange,
                         Set.fromList
                           [PredType
                              [Id [Token "integer" nullRange] [] nullRange,
                               Id [Token "integer" nullRange] [] nullRange],
                            PredType
                              [Id [Token "nonNegativeInteger" nullRange] [] nullRange,
                               Id [Token "nonNegativeInteger" nullRange] [] nullRange]]),
                        (Id
                           [Token "__" nullRange, Token ">" nullRange, Token "__" nullRange]
                           []
                           nullRange,
                         Set.fromList
                           [PredType
                              [Id [Token "integer" nullRange] [] nullRange,
                               Id [Token "integer" nullRange] [] nullRange],
                            PredType
                              [Id [Token "nonNegativeInteger" nullRange] [] nullRange,
                               Id [Token "nonNegativeInteger" nullRange] [] nullRange]]),
                        (Id
                           [Token "__" nullRange, Token ">=" nullRange, Token "__" nullRange]
                           []
                           nullRange,
                         Set.fromList
                           [PredType
                              [Id [Token "integer" nullRange] [] nullRange,
                               Id [Token "integer" nullRange] [] nullRange],
                            PredType
                              [Id [Token "nonNegativeInteger" nullRange] [] nullRange,
                               Id [Token "nonNegativeInteger" nullRange] [] nullRange]]),
                        (Id [Token "even" nullRange] [] nullRange,
                         Set.fromList
                           [PredType [Id [Token "integer" nullRange] [] nullRange],
                            PredType
                              [Id [Token "nonNegativeInteger" nullRange] [] nullRange]]),
                        (Id [Token "odd" nullRange] [] nullRange,
                         Set.fromList
                           [PredType [Id [Token "integer" nullRange] [] nullRange],
                            PredType
                              [Id [Token "nonNegativeInteger" nullRange] [] nullRange]])]}

predefinedAxioms :: [SenAttr (FORMULA ()) [Char]]
predefinedAxioms =
    [
     makeNamed "nothing in Nothing" $
     Quantification Universal
     [Var_decl [mk_Name 1] thing nullRange]
     (
      Negation
      (
       Predication
       noThing
       [Qual_var (mk_Name 1) thing nullRange]
       nullRange
      )
      nullRange
     )
     nullRange
    ,
     makeNamed "thing in Thing" $
     Quantification Universal
     [Var_decl [mk_Name 1] thing nullRange]
     (
       Predication
       (Qual_pred_name (stringToId "Thing")
                           (Pred_type [thing] nullRange) nullRange)
       [Qual_var (mk_Name 1) thing nullRange]
       nullRange
     )
     nullRange
    ]

-- | Build a name
mk_Name :: Int -> Token
mk_Name i = mkSimpleId $ hetsPrefix ++  mk_Name_H i
    where
      mk_Name_H k =
          case k of
            0 -> ""
            j ->  (mk_Name_H (j `div` 26)) ++ [(chr ((j `mod` 26) + 96))]
