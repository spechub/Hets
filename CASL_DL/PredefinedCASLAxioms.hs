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

hetsPrefix :: String
hetsPrefix = ""

-- | OWL topsort Thing
thing :: SORT
thing = stringToId "Thing"

n :: Range
n = nullRange

nothing :: Id
nothing = stringToId "Nothing"

dataId :: Id
dataId = stringToId "DATA"

integer :: Id
integer = stringToId "integer"

posInt :: Id
posInt = stringToId "positiveInteger"

negInt :: Id
negInt = stringToId "negativeInteger"

nonPosInt :: Id
nonPosInt = stringToId "nonPositiveInteger"

nonNegInt :: Id
nonNegInt = stringToId "nonNegativeInteger"

-- | OWL bottom
noThing :: PRED_SYMB
noThing = Qual_pred_name nothing
                         (Pred_type [thing] n) n

predefSign :: CASLSign
predefSign = (emptySign ())
                 { sortRel = Rel.insertKey (stringToId "Char")
                      $ Rel.insertKey dataId
                      $ Rel.transClosure $ Rel.fromList
                       [
                        (stringToId "boolean",
                         dataId),
                        (integer,
                         dataId),
                        (negInt,
                         dataId),
                        (negInt,
                         integer),
                        (negInt,
                         nonPosInt),
                        (nonNegInt,
                         dataId),
                        (nonNegInt,
                         integer),
                        (nonPosInt,
                         dataId),
                        (nonPosInt,
                         integer),
                        (posInt,
                         dataId),
                        (posInt,
                         integer),
                        (posInt,
                         nonNegInt),
                        (posInt,
                         dataId),
                        (posInt,
                         integer),
                        (posInt,
                         nonNegInt),
                        (stringToId "string",
                         dataId)]
                 , predMap =
                     MapSet.fromList
                       [(nothing,
                           [PredType [thing]]),
                        (mkInfix "<",
                           [PredType
                              [integer,
                               integer],
                            PredType
                              [nonNegInt,
                               nonNegInt]]),
                        (mkInfix "<=",
                           [PredType
                              [integer,
                               integer],
                            PredType
                              [nonNegInt,
                               nonNegInt]]),
                        (mkInfix ">",
                           [PredType
                              [integer,
                               integer],
                            PredType
                              [nonNegInt,
                               nonNegInt]]),
                        (mkInfix ">=",
                           [PredType
                              [integer,
                               integer],
                            PredType
                              [nonNegInt,
                               nonNegInt]]),
                        (stringToId "even",
                           [PredType [integer],
                            PredType
                              [nonNegInt]]),
                        (stringToId "odd",
                           [PredType [integer],
                            PredType
                              [nonNegInt]])]}

predefinedAxioms :: [Named (FORMULA ())]
predefinedAxioms = let
  v1 = mkVarDecl (mk_Name 1) thing
  t1 = toQualVar v1
  in
    [
     makeNamed "nothing in Nothing" $
     mkForall
     [v1]
     (
      Negation
      (
       Predication
       noThing
       [t1]
       n
      )
      n
     )
     n
    ,
     makeNamed "thing in Thing" $
     mkForall
     [v1]
     (
       Predication
       (Qual_pred_name thing
                           (Pred_type [thing] n) n)
       [t1]
       n
     )
     n
    ]

-- | Build a name
mk_Name :: Int -> Token
mk_Name i = mkSimpleId $ hetsPrefix ++ mk_Name_H i
    where
      mk_Name_H k =
          case k of
            0 -> ""
            j -> mk_Name_H (j `div` 26) ++ [chr (j `mod` 26 + 96)]
