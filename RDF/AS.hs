{- |
Module      :  $Header$
Copyright   :  (c) Francisc-Nicolae Bungiu
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

RDF abstract syntax

References:
    <http://www.informatik.uni-bremen.de/~till/papers/ontotrans.pdf>
    <http://www.w3.org/TR/rdf-concepts/#section-Graph-syntax>
-}

module RDF.AS where

import Common.Id
import OWL2.Keywords

import Data.Char (intToDigit)
import Data.List
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

-- * URIs

data URIType = Full | Abbreviated | Blank
    deriving (Show, Eq, Ord)

data QName = QN
  { namePrefix :: String
  -- ^ the name prefix part of a qualified name \"namePrefix:localPart\"
  , localPart :: String
  -- ^ the local part of a qualified name \"namePrefix:localPart\"
  , iriType :: URIType
  , expandedIRI :: String
  -- ^ the associated namespace uri (not printed)
  , iriPos :: Range
  } deriving Show

instance Eq QName where
    p == q = compare p q == EQ

instance Ord QName where
  compare (QN p1 l1 b1 n1 _) (QN p2 l2 b2 n2 _) =
    if null n1 || null n2 then compare (b1, p1, l1) (b2, p2, l2) else
      compare n1 n2 -- compare fully expanded names only

instance GetRange QName where
  getRange = iriPos

showQN :: QName -> String
showQN q = (if iriType q /= Abbreviated then showQI else showQU) q

-- | show QName as abbreviated iri
showQU :: QName -> String
showQU (QN pre local _ _ _) =
    if null pre then local else pre ++ ":" ++ local

-- | show QName in ankle brackets as full iris
showQI :: QName -> String
showQI = ('<' :) . (++ ">") . showQU

nullQName :: QName
nullQName = QN "" "" Abbreviated "" nullRange

isNullQName :: QName -> Bool
isNullQName qn = case qn of
    QN "" "" _ "" _ -> True
    _ -> False

dummyQName :: QName
dummyQName =
  QN "http" "//www.dfki.de/sks/hets/ontology/unamed" Full "" nullRange

mkQName :: String -> QName
mkQName s = nullQName { localPart = s }

setQRange :: Range -> QName -> QName
setQRange r q = q { iriPos = r }

setPrefix :: String -> QName -> QName
setPrefix s q = q { namePrefix = s }

setFull :: QName -> QName
setFull q = q {iriType = Full}

type URI = QName

type Datatype = URI
type LanguageTag = String
type LexicalForm = String

-- * LITERALS

data TypedOrUntyped = Typed Datatype | Untyped (Maybe LanguageTag)
    deriving (Show, Eq, Ord)

data Literal = Literal LexicalForm TypedOrUntyped | NumberLit FloatLit
    deriving (Show, Eq, Ord)

-- | non-negative integers given by the sequence of digits
data NNInt = NNInt [Int] deriving (Eq, Ord)

instance Show NNInt where
  show (NNInt l) = map intToDigit l

zeroNNInt :: NNInt
zeroNNInt = NNInt []

isZeroNNInt :: NNInt -> Bool
isZeroNNInt (NNInt l) = null l

data IntLit = IntLit
  { absInt :: NNInt
  , isNegInt :: Bool }
  deriving (Eq, Ord)

instance Show IntLit where
  show (IntLit n b) = (if b then ('-' :) else id) $ show n

zeroInt :: IntLit
zeroInt = IntLit zeroNNInt False

isZeroInt :: IntLit -> Bool
isZeroInt (IntLit n _) = isZeroNNInt n

negNNInt :: Bool -> NNInt -> IntLit
negNNInt b n = IntLit n b

negInt :: IntLit -> IntLit
negInt (IntLit n b) = IntLit n $ not b

data DecLit = DecLit
  { truncDec :: IntLit
  , fracDec :: NNInt }
  deriving (Eq, Ord)

instance Show DecLit where
  show (DecLit t f) = show t
    ++ if isZeroNNInt f then "" else
      '.' : show f

isDecInt :: DecLit -> Bool
isDecInt = isZeroNNInt . fracDec

negDec :: Bool -> DecLit -> DecLit
negDec b (DecLit t f) = DecLit (if b then negInt t else t) f

data FloatLit = FloatLit
  { floatBase :: DecLit
  , floatExp :: IntLit }
  deriving (Eq, Ord)

instance Show FloatLit where
  show (FloatLit b e) = show b
    ++ if isZeroInt e then "" else
      'E' : show e ++ "F"

isFloatDec :: FloatLit -> Bool
isFloatDec = isZeroInt . floatExp

isFloatInt :: FloatLit -> Bool
isFloatInt f = isFloatDec f && isDecInt (floatBase f)

floatToInt :: FloatLit -> IntLit
floatToInt = truncDec . floatBase

intToDec :: IntLit -> DecLit
intToDec i = DecLit i zeroNNInt

decToFloat :: DecLit -> FloatLit
decToFloat d = FloatLit d zeroInt

intToFloat :: IntLit -> FloatLit
intToFloat = decToFloat . intToDec

abInt :: IntLit -> IntLit
abInt int = int {isNegInt = False}

abDec :: DecLit -> DecLit
abDec dec = dec {truncDec = abInt $ truncDec dec}

abFloat :: FloatLit -> FloatLit
abFloat f = f {floatBase = abDec $ floatBase f}

isNegDec :: DecLit -> Bool
isNegDec d = isNegInt $ truncDec d

numberName :: FloatLit -> String
numberName f
    | isFloatInt f = integerS
    | isFloatDec f = decimalS
    | otherwise = floatS

cTypeS :: String
cTypeS = "^^"

-- * Graphs

data Component = Subject | Predicate | Object
    deriving (Show, Eq, Ord)

data Triple = Triple Component (Either URI Literal)
    deriving (Show, Eq, Ord)

data RDFGraph = RDFGraph [Triple]
    deriving (Show, Eq, Ord)
