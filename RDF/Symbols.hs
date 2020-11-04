{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
{- |
Module      :  ./RDF/Symbols.hs
Copyright   :  (c) Francisc-Nicolae Bungiu
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.bungiu@jacobs-university.de
Stability   :  provisional
Portability :  portable

Symbol items for Hets
-}

module RDF.Symbols where

import Common.Id
import Common.IRI
import Data.Data

import GHC.Generics (Generic)
import Data.Hashable

import RDF.AS

-- * SYMBOL ITEMS FOR HETS

data SymbItems = SymbItems (Maybe RDFEntityType) [IRI]
    deriving (Show, Eq, Typeable, Data)

data SymbMapItems = SymbMapItems (Maybe RDFEntityType) [(IRI, Maybe IRI)]
    deriving (Show, Eq, Typeable, Data)

-- | raw symbols
data RawSymb = ASymbol RDFEntity | AnUri IRI
    deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable RawSymb

instance GetRange RawSymb
