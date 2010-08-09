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

data Relation = Sgn
  { decnm :: Token  -- ^ the name
  , desrc :: Concept -- ^ the source concept
  , detrg :: Concept -- ^ the target concept
  } deriving (Eq, Ord, Show)

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

data RuleType = Implication | ReverseImpl | Equivalence deriving (Eq, Ord, Show)

data Rule
  = Rule Expression RuleType Expression
  | Truth Expression
    deriving (Eq, Ord, Show)

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

data KeyDef = KeyDef
  { kdlbl :: Token
  , kdcpt :: Concept
  , kdats :: [KeyAtt]
  } deriving Show

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
