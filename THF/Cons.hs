{- |
Module      :  $Header$
Description :  A collection of data-structures, functions and instances for
                the THF modules.
Copyright   :  (c) A. Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Alexis.Tsogias@dfki.de
Stability   :  provisional
Portability :  portable

Data structures and functions used in Logic_THF and HasCASL2THF.
Note: Some of the implenentations depend on the THF0 Syntax.
-}

module THF.Cons where

import THF.As
import THF.ParseTHF
import THF.ParseTHF0

import Common.Id
import Text.ParserCombinators.Parsec

-- Data structur to differ between the two THF syntaxes
data THFBS =
    BSTHF0 | BSTHF
    deriving (Show, Eq, Ord)

-- Some empty instances

instance GetRange Include

instance GetRange TPTP_THF

instance GetRange AtomicWord

--------------------------------------------------------------------------------
-- BasicSpecTHF
--------------------------------------------------------------------------------

data BasicSpecTHF =
    BasicSpecTHF THFBS [TPTP_THF] --replace THFBS using Sublogic.hs
    deriving (Show, Eq, Ord)

instance GetRange BasicSpecTHF

basicSpec :: THFBS -> CharParser st BasicSpecTHF
basicSpec o = case o of
    BSTHF0    -> fmap (BasicSpecTHF BSTHF0) parseTHF0
    BSTHF     -> fmap (BasicSpecTHF BSTHF) parseTHF

--------------------------------------------------------------------------------
-- SentenceTHF
--------------------------------------------------------------------------------

-- A Sentence is a THFFormula.
data SentenceTHF = Sentence
    { senRole       :: FormulaRole
    , senFormula    :: THFFormula
    , senAnno       :: Annotations }
    deriving (Show, Eq, Ord)

instance GetRange SentenceTHF

instance GetRange THFFormula

--------------------------------------------------------------------------------
-- SymbolTHF
--------------------------------------------------------------------------------

data SymbolTHF = Symbol
    { symId     :: Constant
    , symName   :: Name
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
  | VType Variable
  | ParType Type
    deriving (Show, Ord, Eq)

data Kind =
    Kind
  | MapKind Kind Kind Range
  | SysType SystemType
  | VKind Variable
  | ParKind Kind
    deriving (Show, Ord, Eq)
