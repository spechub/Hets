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
  , nothing
  , conceptPred
  , dataS
  , predefinedAxioms
  , mkNName
  ) where

import CASL.AS_Basic_CASL
import CASL.Sign

import Common.AS_Annotation
import Common.Id
import qualified Common.Lib.Rel as Rel
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

-- | OWL Data topSort DATA
dataS :: Id
dataS = stringToId "DATA"

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

classPredType :: PRED_TYPE
classPredType = Pred_type [thing] n

conceptPred :: PredType
conceptPred = toPredType classPredType

boolS :: Id
boolS = stringToId "boolean"

boolT :: OpType
boolT = mkTotOpType [] boolS

natT :: OpType
natT = mkTotOpType [] nonNegInt

-- | OWL bottom
noThing :: PRED_SYMB
noThing = Qual_pred_name nothing classPredType n

predefSign :: CASLSign
predefSign = (emptySign ())
                 { sortRel = Rel.insertKey (stringToId "Char")
                      $ Rel.insertKey thing
                      $ Rel.transClosure $ Rel.fromList
                       [
                        (boolS,
                         dataS),
                        (integer,
                         dataS),
                        (negInt,
                         dataS),
                        (negInt,
                         integer),
                        (negInt,
                         nonPosInt),
                        (nonNegInt,
                         dataS),
                        (nonNegInt,
                         integer),
                        (nonPosInt,
                         dataS),
                        (nonPosInt,
                         integer),
                        (posInt,
                         dataS),
                        (posInt,
                         integer),
                        (posInt,
                         nonNegInt),
                        (posInt,
                         dataS),
                        (posInt,
                         integer),
                        (posInt,
                         nonNegInt),
                        (stringToId "string",
                         dataS),
                        (dataS, thing) ]
                 , predMap =
                     MapSet.fromList
                       [(nothing,
                           [conceptPred]),
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
                              [nonNegInt]])]
                  , opMap = MapSet.fromList
                        $ map (\ i -> (stringToId $ show i, [natT]))
                          [0 .. 9 :: Int]
                        ++
                        [ (stringToId "True", [boolT])
                        , (stringToId "False", [boolT])
                        , (mkInfix "@@", [mkTotOpType [nonNegInt, nonNegInt]
                                   nonNegInt])
                        , (mkId [mkSimpleId "-", placeTok]
                          , [mkTotOpType [integer] integer])
                        ] }

predefinedAxioms :: [Named (FORMULA ())]
predefinedAxioms = let
  v1 = mkVarDecl (mkNName 1) thing
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
    ,
     makeNamed "thing in Thing" $
     mkForall
     [v1]
     (
       Predication
       (Qual_pred_name thing classPredType n)
       [t1]
       n
     )
    ]

-- | Build a name
mkNName :: Int -> Token
mkNName i = mkSimpleId $ hetsPrefix ++ mkNNameAux i
    where
      mkNNameAux k =
          case k of
            0 -> ""
            j -> mkNNameAux (j `div` 26) ++ [chr (j `mod` 26 + 96)]
