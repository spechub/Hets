{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./OWL2/Symbols.hs
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Symbol items for Hets
-}

module OWL2.Symbols where

import qualified OWL2.AS as AS
import Common.IRI
import Common.Id (Id)

import Data.Data

-- * SYMBOL ITEMS FOR HETS

data ExtEntityType = AnyEntity | PrefixO | EntityType AS.EntityType
  deriving (Show, Eq, Ord, Typeable, Data)

data SymbItems = SymbItems ExtEntityType [IRI]
    deriving (Show, Eq, Typeable, Data)

symbItemsName :: SymbItems -> [String]
symbItemsName (SymbItems _ iris) = 
 map showIRI iris

data SymbMapItems = SymbMapItems ExtEntityType [(IRI, Maybe IRI)]
    deriving (Show, Eq, Typeable, Data)

-- | raw symbols
data RawSymb = ASymbol AS.Entity | AnUri IRI | APrefix String
    deriving (Show, Eq, Ord, Typeable, Data)

idToRaw :: Id -> RawSymb
idToRaw = AnUri . idToIRI
