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
  , predefinedSign
  , predefSign2
  , datatypeSigns
  , thing
  , nothing
  , conceptPred
  , dataPred
  , dataS
  , predefinedAxioms
  , mkNName
  , mkDigit
  , joinDigits
  , negateInt
  , integer
  , float
  , negateFloat
  , posInt
  , nonPosInt
  , decimal
  , double
  , upcast
  , mkDecimal
  , mkFloat
  , consChar
  , emptyStringTerm
  , trueT
  , falseT
  , nonNegInt
  , negIntS
  , stringS
  ) where

import CASL.AS_Basic_CASL
import CASL.Sign
import OWL2.Keywords

import Common.AS_Annotation
import Common.Id
import Common.GlobalAnnotations
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.MapSet as MapSet

import qualified Data.HashMap.Strict as Map

import Data.Char

hetsPrefix :: String
hetsPrefix = ""

-- | OWL topsort Thing
thing :: SORT
thing = stringToId thingS

n :: Range
n = nullRange

nothing :: SORT
nothing = stringToId nothingS

-- | OWL Data topSort DATA
dataS :: SORT
dataS = stringToId dATAS

integer :: SORT
integer = stringToId integerS

float :: SORT
float = stringToId floatS

decimal :: SORT
decimal = stringToId decimalS

double :: SORT
double = stringToId doubleS

posInt :: SORT
posInt = stringToId positiveIntegerS

negIntS :: SORT
negIntS = stringToId negativeIntegerS

nonPosInt :: SORT
nonPosInt = stringToId nonPositiveIntegerS

nonNegInt :: SORT
nonNegInt = stringToId nonNegativeIntegerS

classPredType :: PRED_TYPE
classPredType = Pred_type [thing] n

conceptPred :: PredType
conceptPred = toPredType classPredType

dataPred :: PredType
dataPred = PredType [dataS, dataS]

boolS :: SORT
boolS = stringToId "boolean"

boolT :: OpType
boolT = mkTotOpType [] boolS

trueS :: Id
trueS = stringToId "True"

falseS :: Id
falseS = stringToId "False"

mkConst :: Id -> OpType -> TERM ()
mkConst i o = mkAppl (mkQualOp i $ toOP_TYPE o) []

trueT :: TERM ()
trueT = mkConst trueS boolT

falseT :: TERM ()
falseT = mkConst falseS boolT

natT :: OpType
natT = mkTotOpType [] nonNegInt

-- | create a term of type nonNegativeInteger
mkDigit :: Int -> TERM ()
mkDigit i = mkConst (stringToId $ show i) natT

unMinus :: Id
unMinus = mkId [mkSimpleId "-", placeTok]

minusTy :: OpType
minusTy = mkTotOpType [integer] integer

minusFloat :: OpType
minusFloat = mkTotOpType [float] float

negateTy :: OpType -> TERM () -> TERM ()
negateTy o t = mkAppl (mkQualOp unMinus $ toOP_TYPE o) [t]

-- | negate a term of type integer
negateInt :: TERM () -> TERM ()
negateInt = negateTy minusTy

-- | negate a term of type float
negateFloat :: TERM () -> TERM ()
negateFloat = negateTy minusFloat

atAt :: Id
atAt = mkInfix "@@"

atAtTy :: OpType
atAtTy = mkTotOpType [nonNegInt, nonNegInt] nonNegInt

mkBinOp :: Id -> OpType -> TERM () -> TERM () -> TERM ()
mkBinOp i o t1 t2 = mkAppl (mkQualOp i $ toOP_TYPE o) [t1, t2]

-- | join two terms of type nonNegativeInteger
joinDigits :: TERM () -> TERM () -> TERM ()
joinDigits = mkBinOp atAt atAtTy

dec :: Id
dec = mkInfix ":::"

decTy :: OpType
decTy = mkTotOpType [nonNegInt, nonNegInt] float

{- | create the float given by two non-negative integers separated by the
decimal point -}
mkDecimal :: TERM () -> TERM () -> TERM ()
mkDecimal = mkBinOp dec decTy

eId :: Id
eId = mkInfix "E"

expTy :: OpType
expTy = mkTotOpType [float, integer] float

-- | construct the E float, where the second argument is of type integer
mkFloat :: TERM () -> TERM () -> TERM ()
mkFloat = mkBinOp eId expTy

-- | upcast a term to a matching sort
upcast :: TERM () -> SORT -> TERM ()
upcast t ty = Sorted_term t ty nullRange

charS :: Id
charS = stringToId "Char"

charT :: OpType
charT = mkTotOpType [] charS

stringS :: Id
stringS = stringToId "string"

cons :: Id
cons = mkInfix ":@:"

emptyString :: Id
emptyString = stringToId "emptyString"

emptyStringTerm :: TERM ()
emptyStringTerm = mkAppl (mkQualOp emptyString $ toOP_TYPE emptyStringTy) []

charToId :: Char -> Id
charToId c = let s = show (ord c) in
  stringToId $ "'\\" ++ replicate (3 - length s) '0' ++ show (ord c) ++ "'"

mkChar :: Char -> TERM ()
mkChar c = mkAppl (mkQualOp (charToId c) $ toOP_TYPE charT) []

consChar :: Char -> TERM () -> TERM ()
consChar c t = mkAppl (mkQualOp cons $ toOP_TYPE consTy) [mkChar c, t]

emptyStringTy :: OpType
emptyStringTy = mkTotOpType [] stringS

consTy :: OpType
consTy = mkTotOpType [charS, stringS] stringS

-- | OWL bottom
noThing :: PRED_SYMB
noThing = Qual_pred_name nothing classPredType n

intTypes :: [PredType]
intTypes = map (\ t -> PredType [t]) [integer, nonNegInt]

predefinedSign2 :: e -> Sign f e
predefinedSign2 e = (emptySign e) {
  sortRel = Rel.insertKey thing $ Rel.insertKey dataS Rel.empty
  }

predefSign2 :: CASLSign
predefSign2 = predefinedSign2 ()

-- | instead of one big signature, several small ones

charSign :: CASLSign
charSign = (emptySign ())
                 { sortRel = Rel.insertKey (stringToId "Char") Rel.empty
                 , opMap = MapSet.fromList
                        $  map (\ c -> (charToId c, [charT]))
                          [chr 0 .. chr 127]
                 }

integerSign :: CASLSign
integerSign  = (emptySign ())
                 { sortRel =
                      Rel.transClosure $ Rel.fromList
                       [(negIntS, nonPosInt),
                        (nonNegInt, integer),
                        (nonPosInt, integer),
                        (posInt, nonNegInt),
                        (integer, dataS)]
                 , predMap =
                     MapSet.fromList
                      $ 
                      map ( \ o -> (stringToId o, intTypes))
                         ["even", "odd"]
                 , opMap = MapSet.fromList
                        $ map (\ i -> (stringToId $ show i, [natT]))
                          [0 .. 9 :: Int]
                        ++
                        [ 
                         (atAt, [atAtTy])
                        ]
                 , globAnnos = emptyGlobalAnnos
                     { literal_annos = emptyLiteralAnnos
                       { number_lit = Just atAt
                        }}
                 }



predefinedSign :: e -> Sign f e
predefinedSign e = (emptySign e)
                 { sortRel = Rel.insertKey (stringToId "Char")
                      $ Rel.insertKey thing
                      $ Rel.transClosure $ Rel.fromList
                       [(boolS, dataS),
                        (integer, float),
                        (float, dataS),
                        (negIntS, nonPosInt),
                        (nonNegInt, integer),
                        (nonPosInt, integer),
                        (posInt, nonNegInt),
                        (stringS, dataS) ]
                 , predMap =
                     MapSet.fromList
                      $ (nothing, [conceptPred])
                      : map ((\ o -> (mkInfix o, [dataPred])) .
                         showFacet) facetList
                      ++ map ( \ o -> (stringToId o, intTypes))
                         ["even", "odd"]
                 , opMap = MapSet.fromList
                        $ map (\ i -> (stringToId $ show i, [natT]))
                          [0 .. 9 :: Int]
                        ++ map (\ c -> (charToId c, [charT]))
                          [chr 0 .. chr 127]
                        ++
                        [ (trueS, [boolT])
                        , (falseS, [boolT])
                        , (atAt, [atAtTy])
                        , (unMinus, [minusTy, minusFloat])
                        , (dec, [decTy])
                        , (eId, [expTy])
                        , (cons, [consTy])
                        , (emptyString, [emptyStringTy])
                        ]
                 , globAnnos = emptyGlobalAnnos
                     { literal_annos = emptyLiteralAnnos
                       { number_lit = Just atAt
                       , float_lit = Just (dec, eId)
                       , string_lit = Just (emptyString, cons) }}
                 }

floatSign :: CASLSign
floatSign = integerSign
                 { sortRel = Rel.union (sortRel integerSign) 
                      $ Rel.transClosure $ Rel.fromList
                       [
                        (integer, float),
                        (float, dataS)
                        ]
                 
                 , opMap = MapSet.union (opMap integerSign) $ MapSet.fromList
                        $ 
                        [
                          (unMinus, [minusTy, minusFloat])
                        , (dec, [decTy])
                        , (eId, [expTy])
                        ]
                 , globAnnos = (globAnnos integerSign)
                     { literal_annos = (literal_annos $ globAnnos integerSign)
                       {  float_lit = Just (dec, eId)
                        }}
                 }

boolSign :: CASLSign
boolSign = (emptySign ())
                 { sortRel =  Rel.transClosure $ Rel.fromList
                       [(boolS, dataS)]
                 , opMap = MapSet.fromList
                        $ 
                        [ (trueS, [boolT])
                        , (falseS, [boolT])
                        ]
                 }

stringSignAux :: CASLSign
stringSignAux = (emptySign ())
                 { sortRel = 
                      Rel.transClosure $ Rel.fromList
                       [ (stringS, dataS) ]
                 , opMap = MapSet.fromList
                        $ 
                        [
                         (emptyString, [emptyStringTy])
                         , (cons, [consTy])
                        ]
                 , globAnnos = emptyGlobalAnnos
                     { literal_annos = emptyLiteralAnnos
                       { 
                       string_lit = Just (emptyString, cons) }}
                 }

stringSign :: CASLSign
stringSign = uniteCASLSign stringSignAux charSign

datatypeSigns :: Map.HashMap SORT CASLSign
datatypeSigns = Map.fromList
   [ (charS, charSign)
   , (integer, integerSign)
   , (float, floatSign)
   , (boolS, boolSign)
   , (stringS, stringSign)]

predefSign :: CASLSign
predefSign = predefinedSign ()

predefinedAxioms :: [Named (FORMULA ())]
predefinedAxioms = let
  v1 = mkVarDecl (mkNName 1) thing
  t1 = toQualVar v1
  in [makeNamed "nothing in Nothing" $ mkForall [v1] $ Negation
            (Predication noThing [t1] n) n,
      makeNamed "thing in Thing" $ mkForall [v1] $ Predication
            (Qual_pred_name thing classPredType n) [t1] n]

mkNNameAux :: Int -> String
mkNNameAux k = genNamePrefix ++ "x" ++ show k

-- | Build a name
mkNName :: Int -> Token
mkNName i = mkSimpleId $ hetsPrefix ++ mkNNameAux i
