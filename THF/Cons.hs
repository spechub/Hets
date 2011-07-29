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

import Common.Id
import Text.ParserCombinators.Parsec

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
    ST_Const Type
  | ST_Type Kind
    deriving (Show, Eq, Ord)

data Type =
    TType
  | OType
  | IType
  | MapType Type Type
  | CType Constant
  | SType SystemType
    deriving (Show, Ord, Eq)

data Kind =
    Kind
  | MapKind Kind Kind Range
  | SysType SystemType
    deriving (Show, Ord, Eq)

hasSysType :: Kind -> Bool
hasSysType k = case k of
    MapKind k1 k2 _ -> hasSysType k1 || hasSysType k2
    SysType _       -> True
    _               -> False
