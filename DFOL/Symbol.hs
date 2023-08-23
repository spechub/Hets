{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./DFOL/Symbol.hs
Description :  Symbol definition for first-order logic with
               dependent types
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module DFOL.Symbol where

import DFOL.AS_DFOL

import Common.Id
import Common.Doc
import Common.DocUtils

import Data.Data
import qualified Data.Map as Map

-- a symbol is just a name
data Symbol = Symbol {name :: NAME} deriving (Show, Eq, Ord, Typeable, Data)

-- pretty printing
instance Pretty Symbol where
    pretty = printSymbol

instance GetRange Symbol where
  getRange = getRange . name

printSymbol :: Symbol -> Doc
printSymbol (Symbol s) = pretty s

-- interface to name maps
toSymMap :: Map.Map NAME NAME -> Map.Map Symbol Symbol
toSymMap map1 = Map.fromList $ map (\ (k, a) -> (Symbol k, Symbol a))
                 $ Map.toList map1

toNameMap :: Map.Map Symbol Symbol -> Map.Map NAME NAME
toNameMap map1 = Map.fromList $ map (\ (Symbol k, Symbol a) -> (k, a))
                    $ Map.toList map1

-- interface to Id
toId :: Symbol -> Id
toId sym = mkId [name sym]

fromId :: Id -> Symbol
fromId (Id toks _ _) = Symbol $ Token (concatMap tokStr toks) nullRange
