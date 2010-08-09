{- |
Module      :  $Header$
Description :  abstract ADL syntax
Copyright   :  (c) Stef Joosten, Christian Maeder DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module Adl.As where

import Data.Char
import Common.Id

data Concept
  = C Token -- ^ The name of this Concept
  | Anything -- ^ Really anything as introduced by I and V
    deriving (Eq, Ord, Show)

instance GetRange Concept where
    getRange c = case c of
      C t -> getRange t
      Anything -> nullRange
    rangeSpan c = case c of
      C t -> rangeSpan t
      Anything -> []

data Relation = Sgn
  { decnm :: Token  -- ^ the name
  , desrc :: Concept -- ^ the source concept
  , detrg :: Concept -- ^ the target concept
  } deriving (Eq, Ord, Show)

instance GetRange Relation where
    getRange = getRange . decnm
    rangeSpan (Sgn t c1 c2) =
      joinRanges [rangeSpan t, rangeSpan c1, rangeSpan c2]

data UnOp
  = K0 -- ^ Reflexive and transitive closure *
  | K1 -- ^ Transitive closure +
  | Cp -- ^ Complement -
  | Co -- ^ Converse ~
    deriving (Eq, Ord, Show)

data MulOp
  = Fc -- ^ composition ;
  | Fd -- ^ relative addition !
  | Fi -- ^ intersection /\.
  | Fu -- ^ union \/
    deriving (Eq, Ord, Show)

data Expression
  = Tm Relation
  | MulExp MulOp [Expression]
  | UnExp UnOp Expression
    deriving (Eq, Ord, Show)

instance GetRange Expression where
  getRange e = case e of
    Tm r -> getRange r
    UnExp _ f -> getRange f
    MulExp _ es -> concatMapRange getRange es
  rangeSpan e = case e of
    Tm r -> rangeSpan r
    UnExp _ f -> rangeSpan f
    MulExp _ es -> joinRanges $ map rangeSpan es

data RuleType = Implication | ReverseImpl | Equivalence deriving (Eq, Ord, Show)

data Rule
  = Rule Expression RuleType Expression
  | Truth Expression
    deriving (Eq, Ord, Show)

instance GetRange Rule where
  getRange r = case r of
    Rule e1 _ e2 -> concatMapRange getRange [e1, e2]
    Truth e -> getRange e
  rangeSpan r = case r of
    Rule e1 _ e2 -> joinRanges [rangeSpan e1, rangeSpan e2]
    Truth e -> rangeSpan e

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
    deriving (Enum, Eq, Ord, Show)

showUp :: Show a => a -> String
showUp = map toUpper . show

allProps :: [Prop]
allProps = [Uni .. Rfx]

data RangedProp = RangedProp
  { propProp :: Prop
  , propRange :: Range }
    deriving (Eq, Ord, Show) -- should be fine since ranges are always equal

instance GetRange RangedProp where
   getRange = propRange
   rangeSpan (RangedProp p r) = tokenRange (Token (show p) r)

-- | create a ranged property
rProp :: Prop -> RangedProp
rProp p = RangedProp p nullRange

data Object = Object
  { label :: Token
  , expr :: Expression
  , props :: [RangedProp]
  , subobjs :: [Object]
  } deriving Show

data KeyAtt = KeyAtt (Maybe Token) Expression deriving Show

instance GetRange KeyAtt where
  getRange (KeyAtt _ e) = getRange e
  rangeSpan (KeyAtt _ e) = rangeSpan e

data KeyDef = KeyDef
  { kdlbl :: Token
  , kdcpt :: Concept
  , kdats :: [KeyAtt]
  } deriving Show

instance GetRange KeyDef where
  getRange (KeyDef _ c _) = getRange c
  rangeSpan (KeyDef _ c as) = joinRanges [rangeSpan c, rangeSpan as]

data RuleKind = SignalOn | Signals | Maintains deriving (Eq, Ord, Show)

showRuleKind :: RuleKind -> String
showRuleKind k = if k == SignalOn then "ON"
             else showUp k

data RuleHeader = Always | RuleHeader RuleKind Token deriving Show

data Pair = Pair Token Token deriving Show

data Plugin = Service | Sqlplug | Phpplug deriving Show

data PatElem
  = Pr RuleHeader Rule
  | Pg Concept Concept -- specific and generic concept
  | Pk KeyDef
  | Pm [RangedProp] Relation Bool -- True indicates population
  | Plug Plugin Object
  | Population Bool Relation [Pair] -- True indicates declaration
    deriving Show

data Context = Context (Maybe Token) [PatElem] deriving Show

instance GetRange Context where
  getRange (Context mt _) = getRange mt
