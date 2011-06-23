{- |
Module      :  $Header$
Description :  A collection of data-structures and functions. e.g SingTHF, SymbolTHF
Copyright   :  (c) A. Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Alexis.Tsogias@dfki.de
Stability   :  provisional
Portability :  portable

Data structures and functions used in Logic_THF and HasCASL2THF
-}

{-
Notes for the developer:
-- lookup monads due to the state monad
-- realworldhaskell monad

-}

module THF.Cons where

import THF.As
import THF.PrintTHF

import Common.DefaultMorphism
import Common.DocUtils
import Common.Id
import Common.GlobalAnnotations
import Common.Result

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel

-- We use the DefaultMorphism for THF.
type MorphismTHF = DefaultMorphism SignTHF

data BasicSpecTHF = BasicSpecTHF [TPTP_THF] deriving (Show, Eq, Ord)

instance GetRange BasicSpecTHF

instance Pretty BasicSpecTHF where
    pretty (BasicSpecTHF a) = printTPTPTHF a


-- Sentence

-- A Sentence is a THFFormula.
type SentenceTHF = THFFormula

instance GetRange THFFormula

instance Pretty THFFormula where
  pretty = printTHF

-- SymbolTHF

data SymbolTHF = Symbol
    { symName :: Id
    , symType :: SymbolType
    } deriving (Show, Eq, Ord)

instance GetRange SymbolTHF

instance Pretty SymbolTHF where
  pretty = undefined

data SymbolType =
    ST_Const
  | ST_Type
  | ST_SubType
    deriving (Show, Eq, Ord)

-- SignTHF

data SignTHF = Sign
    { types :: TypeMap
    , subTypes :: Rel.Rel Id
    , consts :: ConstMap
    , symbols :: Set.Set SymbolTHF
    , annoMap :: Map.Map Id Annotations -- ^ annotated symbols
    , globAnnos :: GlobalAnnos -- ^ global annotations to use
    } deriving (Show, Eq)

instance Ord SignTHF where
    compare s1 s2 = compare
        (types s1, subTypes s1, consts s1, symbols s1, annoMap s1)
        (types s2, subTypes s2, consts s2, symbols s2, annoMap s2)

instance Pretty SignTHF where
    pretty = undefined

type TypeMap = Map.Map Id Kind

type ConstMap = Map.Map Id SentenceTHF

data Kind =
    Kind
  | FunKind Kind Kind Range
    deriving (Show, Ord, Eq)

-- Creates an empty Signature.
emptySign :: SignTHF
emptySign = Sign
    { types = Map.empty
    , subTypes = Rel.empty
    , consts = Map.empty
    , symbols = Set.empty
    , annoMap = Map.empty
    , globAnnos = emptyGlobalAnnos }

sigUnion :: SignTHF -> SignTHF -> Result SignTHF
sigUnion = undefined

sigDiff :: SignTHF -> SignTHF -> Result SignTHF
sigDiff = undefined

sigIntersect :: SignTHF -> SignTHF -> Result SignTHF
sigIntersect = undefined
