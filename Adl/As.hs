{- |
Module      :  $Header$
Description :  abstract ADL syntax
Copyright   :  (c) Christian Maeder DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module Adl.As where

import Data.Char

data Concept
  = C String -- ^ The name of this Concept
  | Anything -- ^ Really Anything!
  | NOthing -- ^ Nothing at all
    deriving (Eq, Ord, Show)

data Relation = Sgn
  { decnm   :: String  -- ^ the name
  , desrc   :: Concept -- ^ the source concept
  , detrg   :: Concept -- ^ the target concept
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
  | Fi -- ^ intersection
  | Fu -- ^ union \/
    deriving (Eq, Ord, Show)

data Expression
  = Tm Relation
  | MulExp MulOp [Expression]
  | UnExp UnOp Expression
    deriving (Eq, Ord, Show)

data RuleType = Implication | Equivalence deriving (Eq, Ord, Show)

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
    deriving (Enum, Eq, Ord, Show)

showProp :: Prop -> String
showProp = map toUpper . show

allProps :: [Prop]
allProps = [Uni .. Rfx]

data PatElem
  = Pr Rule
  | Pg Concept Concept -- generic and specific concept
  | Pm [Prop] Relation
  | Ignored
    deriving Show
