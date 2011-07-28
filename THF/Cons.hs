{- |
Module      :  $Header$
Description :  A collection of data-structures and functions.
                e.g SingTHF, SymbolTHF
Copyright   :  (c) A. Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Alexis.Tsogias@dfki.de
Stability   :  provisional
Portability :  portable

Data structures and functions used in Logic_THF and HasCASL2THF
Note: Most of the implenentations use the THF0 Syntax.
-}

{-
Notes for the developer:
-- lookup monads due to the state monad
-- realworldhaskell monad

-}

module THF.Cons where

import THF.As
import THF.ParseTHF
import THF.ParseTHF0

import Common.DefaultMorphism
import Common.Id
import Common.GlobalAnnotations
import Common.Result
import Text.ParserCombinators.Parsec

import qualified Data.Map as Map

-- We use the DefaultMorphism for THF.
type MorphismTHF = DefaultMorphism SignTHF

data THFBS =
    BSTHF0 | BSTHF
    deriving (Show, Eq, Ord)

data BasicSpecTHF =
    BasicSpecTHF THFBS [TPTP_THF]
    deriving (Show, Eq, Ord)

instance GetRange BasicSpecTHF

basicSpec :: THFBS -> CharParser st BasicSpecTHF
basicSpec o = case o of
    BSTHF0    -> fmap (BasicSpecTHF BSTHF0) parseTHF0
    BSTHF     -> fmap (BasicSpecTHF BSTHF) parseTHF


-- Some other instances

instance GetRange Include

instance GetRange TPTP_THF

instance GetRange AtomicWord

-- Sentence

-- A Sentence is a THFFormula.
type SentenceTHF = THFFormula

instance GetRange THFFormula

-- SymbolTHF

data SymbolTHF = Symbol
    { symName   :: Constant
    , symType   :: SymbolType
    } deriving (Show, Eq, Ord)

instance GetRange SymbolTHF

data SymbolType =
    ST_Const
  | ST_Type
    deriving (Show, Eq, Ord)

-- SignTHF
data SignTHF = Sign
    { types :: TypeMap
    , consts :: ConstMap
    , symbols :: SymbolMap
    , annoMap :: Map.Map Id Annotations -- ^ annotated symbols
    , globAnnos :: GlobalAnnos -- ^ global annotations to use
    } deriving (Show, Eq)

instance Ord SignTHF where
    compare s1 s2 = compare
        (types s1, consts s1, symbols s1, annoMap s1)
        (types s2, consts s2, symbols s2, annoMap s2)

instance GetRange SignTHF

type TypeMap = Map.Map Constant TypeInfo

type ConstMap = Map.Map Constant ConstInfo

type SymbolMap = Map.Map Constant SymbolTHF

data TypeInfo = TypeInfo
    { typeName  :: Constant
    , typeKind  :: Kind
    , typeDef   :: THFTypedConst }
    deriving (Show, Ord, Eq)

data ConstInfo = ConstInfo
    { constName :: Constant
    , constKind :: Kind
    , constDef  :: THFTypedConst }
    deriving (Show, Ord, Eq)

data Kind =
    TType
  | FunKind Kind Kind Range
  | Const Constant
  | SysType SystemType
    deriving (Show, Ord, Eq)

-- This method checks weather a kind does not contain any
isFinishedKind :: Kind -> Bool
isFinishedKind k = case k of
    FunKind k1 k2 _ -> isFinishedKind k1 && isFinishedKind k2
    TType           -> True
    SysType _       -> True
    _               -> False

hasSysType :: Kind -> Bool
hasSysType k = case k of
    FunKind k1 k2 _ -> hasSysType k1 || hasSysType k2
    SysType _       -> True
    _               -> False

-- Creates an empty Signature.
emptySign :: SignTHF
emptySign = Sign
    { types = Map.empty
    , consts = Map.empty
    , symbols = Map.empty
    , annoMap = Map.empty
    , globAnnos = emptyGlobalAnnos }

sigUnion :: SignTHF -> SignTHF -> Result SignTHF
sigUnion = undefined

sigDiff :: SignTHF -> SignTHF -> Result SignTHF
sigDiff = undefined

sigIntersect :: SignTHF -> SignTHF -> Result SignTHF
sigIntersect = undefined
