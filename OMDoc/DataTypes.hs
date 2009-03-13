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
               | TLView OMCD OMCD
                 deriving (Show, Eq, Ord)

-- | Theory constitutive elements for OMDoc
data TCElement =
    -- | An axiom or theorem element
    TCAxiomOrTheorem Bool String OMElement
    -- | Symbol to represent sorts, constants, predicate symbols, etc.
  | TCSymbol String (Maybe OMElement) SymbolRole
    -- | Algebraic Data Type represents free/generated types
  | TCADT [OmdADT]
    -- | Import statements for referencing other theories
  | TCImport OMCD
    -- | A comment, only for development purposes
  | TCComment String
    deriving (Show, Eq, Ord)


-- | The flattened structure of an Algebraic Data Type
data OmdADT =
    -- | A single sort given by name, free? and a list of constructors
    ADTSortDef String Bool [OmdADT]
    -- | A constructor given by its name and a list of arguments
  | ADTConstr String [OmdADT]
    -- | An argument with type and evtually a selector
  | ADTArg OMElement (Maybe OmdADT)
    -- | The selector has a name and is total (True) or partial (False)
  | ADTSelector String Bool
    -- | Insort elements point to other sortdefs and inherit their structure
  | ADTInsort String
    deriving (Show, Eq, Ord)

-- | Roles of the declared symbols can be object or type
data SymbolRole = Obj | Typ deriving (Eq, Ord)

instance Show SymbolRole where
    show Obj = "object"
    show Typ = "type"

-- | Names used for OpenMath variables and symbols
data OMName = OMName { name :: String } deriving (Show, Eq, Ord)

-- | Attribute-name/attribute-value pair used to represent the type
-- of a type-annotated term
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

