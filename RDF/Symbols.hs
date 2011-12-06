{- |
Module      :  $Header$
Copyright   :  (c) Francisc-Nicolae Bungiu
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.bungiu@jacobs-university.de
Stability   :  provisional
Portability :  portable

Symbol items for Hets
-}

module RDF.Symbols where

import Common.Id

import RDF.AS
import OWL2.AS

-- * SYMBOL ITEMS FOR HETS

data SymbItems = SymbItems (Maybe RDFEntityType) [IRI]
    deriving (Show, Eq)

data SymbMapItems = SymbMapItems (Maybe RDFEntityType) [(IRI, Maybe IRI)]
    deriving (Show, Eq)

-- | raw symbols
data RawSymb = ASymbol RDFEntity | AnUri IRI
    deriving (Show, Eq, Ord)
    
instance GetRange RawSymb
    
symbItems = undefined

symbMapItems = undefined
