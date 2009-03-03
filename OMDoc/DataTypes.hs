{- |
Module      :  $Header$
Description :  The OMDoc Data Types
Copyright   :  (c) Ewaryst Schulz, DFKI 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  provisional
Portability :  portable

Datatypes for an intermediate OMDoc Representation.
-}
module OMDoc.DataTypes where

{-
  OMDoc represented in 3 layers:
  1. toplevel (theory, view)
  2. theory constitutive (axiom, symbol)
  3. subelements (FMP, Insort) and OpenMath
-}




-- | OMDoc root element with libname and a list of toplevel elements
data OMDoc = OMDoc String [TLElement]

-- | Toplevel elements for OMDoc
data TLElement = TLTheory String [TCElement]
               | TLView
                 deriving (Show, Eq, Ord)

-- | Theory constitutive elements for OMDoc
data TCElement = TCAxiomOrTheorem Bool String OMElement
               | TCComment String
               | TCSymbol String OMElement
               | TCImport
                 deriving (Show, Eq, Ord)

-- | Names used for OpenMath variables and symbols
data OMName = OMName { name :: String } deriving (Show, Eq, Ord)

-- | Attribute-name/attribute-value pair used to represent the type
-- of an type-annotated term
data OMAttribute = OMAttr OMElement OMElement
                      deriving (Show, Eq, Ord)

-- | CD contains the reference to the content dictionary
-- and eventually the cdbase entry
data OMCD = CD { cd :: String,
                 cdbase :: (Maybe String)}
            deriving (Show, Eq, Ord)

-- | Elements for Open Math
data OMElement =
    -- | Symbol
    OMS OMCD OMName
    -- | Simple variable
  | OMV OMName
    -- | Attributed element needed for type annotations of elements
  | OMATTT OMElement OMAttribute
    -- | Application to a list of arguments,
    -- first argument is usually the functionhead
  | OMA [OMElement]
    -- | Bindersymbol, bound vars, body
  | OMBIND OMElement [OMElement] OMElement
  deriving (Show, Eq, Ord)

