{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
{- |
Module      :  ./Adl/As.hs
Description :  abstract ADL syntax
Copyright   :  (c) Stef Joosten, Christian Maeder DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module Adl.As where

import Data.Char
import Data.Data
import Data.List (sortBy)

import Common.Id
import Common.Keywords

import GHC.Generics (Generic)
import Data.Hashable

data Concept
  = C Token -- ^ The name of this Concept
  | Anything -- ^ Really anything as introduced by I and V
    deriving (Eq, Ord, Show, Typeable, Data, Generic)

instance Hashable Concept

instance GetRange Concept where
    getRange c = case c of
      C t -> getRange t
      Anything -> nullRange
    rangeSpan c = case c of
      C t -> rangeSpan t
      Anything -> []

data RelType = RelType
  { relSrc :: Concept -- ^ the source concept
  , relTrg :: Concept -- ^ the target concept
  } deriving (Eq, Ord, Show, Typeable, Data, Generic)

instance Hashable RelType

instance GetRange RelType where
    getRange = getRange . relSrc
    rangeSpan (RelType c1 c2) =
      joinRanges [rangeSpan c1, rangeSpan c2]

data Relation = Sgn
  { decnm :: Token  -- ^ the name
  , relType :: RelType
  } deriving (Eq, Ord, Show, Typeable, Data, Generic)

instance Hashable Relation

instance GetRange Relation where
    getRange = getRange . decnm
    rangeSpan (Sgn n t) =
      joinRanges [rangeSpan n, rangeSpan t]

-- | builtin relation over Anything
bRels :: [String]
bRels = ["I", "V"]

isBRel :: String -> Bool
isBRel s = elem s bRels

data UnOp
  = K0 -- ^ Reflexive and transitive closure *
  | K1 -- ^ Transitive closure +
  | Cp -- ^ Complement -
  | Co -- ^ Converse ~
    deriving (Eq, Ord, Typeable, Data, Generic)

instance Hashable UnOp

instance Show UnOp where
  show o = case o of
    K0 -> "*"
    K1 -> "+"
    Cp -> "-" -- prefix!
    Co -> "~"

data MulOp
  = Fc -- ^ composition ;
  | Fd -- ^ relative addition !
  | Fi -- ^ intersection /\.
  | Fu -- ^ union \/
  | Ri -- ^ Rule implication |-
  | Rr -- ^ Rule reverse implication -|
  | Re -- ^ Rule equivalence
    deriving (Eq, Ord, Typeable, Data, Generic)

instance Hashable MulOp

instance Show MulOp where
  show o = case o of
    Fc -> ";"
    Fd -> "!"
    Fi -> lAnd
    Fu -> lOr
    Ri -> "|-"
    Rr -> "-|"
    Re -> "="

data Rule
  = Tm Relation
  | MulExp MulOp [Rule]
  | UnExp UnOp Rule
    deriving (Eq, Ord, Show, Typeable, Data, Generic)

instance Hashable Rule

instance GetRange Rule where
  getRange e = case e of
    Tm r -> getRange r
    UnExp _ f -> getRange f
    MulExp _ es -> concatMapRange getRange es
  rangeSpan e = case e of
    Tm r -> rangeSpan r
    UnExp _ f -> rangeSpan f
    MulExp _ es -> joinRanges $ map rangeSpan es

data Prop
  = Uni          -- ^ univalent
  | Inj          -- ^ injective
  | Sur          -- ^ surjective
  | Tot          -- ^ total
  | Sym          -- ^ symmetric
  | Asy          -- ^ antisymmetric
  | Trn          -- ^ transitive
  | Rfx          -- ^ reflexive
  | Prop         -- ^ meta property
    deriving (Enum, Eq, Ord, Show, Typeable, Data, Generic)

instance Hashable Prop

showUp :: Show a => a -> String
showUp = map toUpper . show

allProps :: [Prop]
allProps = [Uni .. Rfx]

data RangedProp = RangedProp
  { propProp :: Prop
  , propRange :: Range }
    deriving (Eq, Ord, Show, Typeable, Data, Generic)
  -- should be fine since ranges are always equal

instance Hashable RangedProp

instance GetRange RangedProp where
   getRange = propRange
   rangeSpan (RangedProp p r) = tokenRange (Token (show p) r)

-- | create a ranged property
rProp :: Prop -> RangedProp
rProp p = RangedProp p nullRange

data Object = Object
  { label :: Token
  , expr :: Rule
  , props :: [RangedProp]
  , subobjs :: [Object]
  } deriving (Show, Typeable, Data)

data KeyAtt = KeyAtt (Maybe Token) Rule deriving (Show, Typeable, Data)

instance GetRange KeyAtt where
  getRange (KeyAtt _ e) = getRange e
  rangeSpan (KeyAtt _ e) = rangeSpan e

data KeyDef = KeyDef
  { kdlbl :: Token
  , kdcpt :: Concept
  , kdats :: [KeyAtt]
  } deriving (Show, Typeable, Data)

instance GetRange KeyDef where
  getRange (KeyDef _ c _) = getRange c
  rangeSpan (KeyDef _ c as) = joinRanges [rangeSpan c, rangeSpan as]

data RuleKind = SignalOn | Signals | Maintains
  deriving (Eq, Ord, Show, Typeable, Data, Generic)

instance Hashable RuleKind

showRuleKind :: RuleKind -> String
showRuleKind k = if k == SignalOn then "ON"
             else showUp k

data RuleHeader = Always | RuleHeader RuleKind Token
  deriving (Eq, Show, Typeable, Data)

data Pair = Pair Token Token deriving (Show, Typeable, Data)

data Plugin = Service | Sqlplug | Phpplug deriving (Show, Typeable, Data)

data PatElem
  = Pr RuleHeader Rule
  | Pg Concept Concept -- specific and generic concept
  | Pk KeyDef
  | Pm [RangedProp] Relation Bool -- True indicates population
  | Plug Plugin Object
  | Population Bool Relation [Pair] -- True indicates declaration
    deriving (Show, Typeable, Data)

data Context = Context (Maybe Token) [PatElem] deriving (Show, Typeable, Data)

instance GetRange Context where
  getRange (Context mt _) = getRange mt

comparePatElem :: PatElem -> PatElem -> Ordering
comparePatElem p1 p2 = case (p1, p2) of
  (Pm {}, Pm {}) -> EQ
  (Pm _ _ True, Population True _ _) -> EQ
  (Pm {}, _) -> LT
  (Population True _ _, Pm _ _ True) -> EQ
  (Population True _ _, _) -> LT
  (_, Pm {}) -> GT
  (_, Population True _ _) -> GT
  (Pg {}, Pg {}) -> EQ
  (Pg {}, _) -> LT
  (_, Pg {}) -> GT
  _ -> EQ

mkContext :: Maybe Token -> [PatElem] -> Context
mkContext m = Context m . sortBy comparePatElem
