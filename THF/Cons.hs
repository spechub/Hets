{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
{- |
Module      :  ./THF/Cons.hs
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

import Common.Id

import Data.Data

import GHC.Generics (Generic)
import Data.Hashable

-- Some empty instances

{- -----------------------------------------------------------------------------
BasicSpecTHF
----------------------------------------------------------------------------- -}

data BasicSpecTHF =
    BasicSpecTHF [TPTP_THF]
    deriving (Show, Eq, Ord, Typeable, Data)

instance GetRange BasicSpecTHF

{- -----------------------------------------------------------------------------
SymbolTHF
----------------------------------------------------------------------------- -}

data SymbolTHF = Symbol
    { symId :: Constant
    , symName :: Name
    , symType :: SymbolType
    } deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable SymbolTHF

instance GetRange SymbolTHF

data SymbolType =
    ST_Const Type
  | ST_Type Kind
    deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable SymbolType

data Type =
    TType
  | OType
  | IType
  | MapType Type Type
  | ProdType [Type]
  | CType Constant
  | SType Token
  | VType Token
  | ParType Type
    deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable Type

data Kind = Kind
 deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable Kind
