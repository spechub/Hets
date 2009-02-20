{- |
Module      :  $Header$
Description :  The OMDoc Data Types
Copyright   :  (c) Ewaryst Schulz, DFKI 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  provisional
Portability :  portable

data types for OMDoc
-}
module OMDoc.DataTypes where

{-
  OMDoc represented in 3 layers:
  1. toplevel (theory, view)
  2. theory constitutive (axiom, symbol)
  3. subelements (FMP, Insort) and OpenMath
-}




-- | OMDoc root element with libname and children
data OMDoc = OMDoc String [TLElement]

-- | Top level elements for OMDoc
data TLElement = TLTheory String [TCElement]
               | TLView
                 deriving (Show, Eq, Ord)

-- | Theory constitutive elements for OMDoc
data TCElement = TCAxiomOrTheorem Bool String OMElement
               | TCSymbol String OMElement
               | TCImport
                 deriving (Show, Eq, Ord)

-- | Names used for OpenMath variables and symbols
data OMName = OMName String deriving (Show, Eq, Ord)

-- | attribute-name attribute-value pair
data OMAttribute = OMAttr OMElement OMElement
                      deriving (Show, Eq, Ord)

-- | CD contains the reference to the content dictionary
-- | as name and eventually the CDBase entry
data OMCD = CD String (Maybe String) deriving (Show, Eq, Ord)

-- | Elements for Open Math
data OMElement =
    -- | Symbol
    OMS OMCD OMName
    -- | Simple variable
  | OMV OMName
    -- | Attributed element needed for type annotations of elements
  | OMATTT OMElement OMAttribute
    -- | Application to a list of arguments,
    -- | first argument is usually the functionhead
  | OMA [OMElement]
    -- | Bindersymbol, bound vars, body
  | OMBIND OMElement [OMElement] OMElement
    -- | Comment
  | OMC String
  deriving (Show, Eq, Ord)

