{- |
Module      :  $Header$
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Symbol items for Hets
-}

module OWL2.Symbols where

import OWL2.AS

-- * SYMBOL ITEMS FOR HETS

data ExtEntityType = AnyEntity | Prefix | EntityType EntityType
  deriving (Show, Eq, Ord)

data SymbItems = SymbItems ExtEntityType [IRI]
    deriving (Show, Eq)

data SymbMapItems = SymbMapItems ExtEntityType [(IRI, Maybe IRI)]
    deriving (Show, Eq)

-- | raw symbols
data RawSymb = ASymbol Entity | AnUri IRI | APrefix String
    deriving (Show, Eq, Ord)
