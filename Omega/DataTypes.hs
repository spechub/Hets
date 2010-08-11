{- |
Module      :  $Header$
Description :  The Omega Data Types
Copyright   :  (c) Ewaryst Schulz, DFKI 2008
License     :  GPLv2 or higher

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  provisional
Portability :  portable

Datatypes for an intermediate Omega Representation.
-}
module Omega.DataTypes where

justWhen:: Bool -> a -> Maybe a
justWhen b x = if b then Just x else Nothing

-- | Top level element with libname and a list of theories
data Library = Library String [Theory] deriving (Show, Eq, Ord)

-- | Contains a theoryname a list of imports, signature elements and
-- sentences (axioms or theorems)
data Theory = Theory String [String] [TCElement]
                 deriving (Show, Eq, Ord)

-- | Theory constitutive elements
data TCElement =
    -- | An axiom or theorem element
    TCAxiomOrTheorem Bool String Term
    -- | Symbol to represent sorts, constants, predicate symbols, etc.
  | TCSymbol String
    -- | A comment, only for development purposes
  | TCComment String
    deriving (Show, Eq, Ord)



-- | Term structure
data Term =
    -- | Symbol
    Symbol String
    -- | Simple variable
  | Var String
    -- | Application of a function to a list of arguments
  | App Term [Term]
    -- | Bindersymbol, bound vars, body
  | Bind String [Term] Term
  deriving (Show, Eq, Ord)

