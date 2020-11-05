{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
{- |
Module      :  ./CommonLogic/Symbol.hs
Description :  Symbols of common logic
Copyright   :  (c) Karl Luc, DFKI Bremen 2010, Eugen Kuksa, Uni Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  eugenk@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Definition of symbols for common logic
-}

module CommonLogic.Symbol (
        Symbol (..)
       , printSymbol
       , symOf
       , getSymbolMap
       , getSymbolName
       , symbolToRaw
       , idToRaw
       , matches
       , addSymbToSign
       , symKind
       )
       where

import qualified Common.Id as Id
import Common.Doc
import Common.DocUtils
import Common.Result

import Data.Data
import qualified Data.Set as Set
import qualified Data.HashMap.Lazy as Map

import qualified CommonLogic.Sign as Sign
import CommonLogic.Morphism as Morphism

import GHC.Generics (Generic)
import Data.Hashable

newtype Symbol = Symbol {symName :: Id.Id}
                 deriving (Show, Eq, Ord, Typeable, Generic)

instance Hashable Symbol

instance Id.GetRange Symbol where
    getRange = Id.getRange . symName

instance Pretty Symbol where
    pretty = printSymbol

-- | Pretty prints the symbol @x@
printSymbol :: Symbol -> Doc
printSymbol x = pretty $ symName x

-- | Converts a signature to a set of symbols
symOf :: Sign.Sign -> Set.Set Symbol
symOf x = Set.fold (\ y -> Set.insert Symbol {symName = y}) Set.empty $
           Sign.allItems x

-- | Determines the symbol map of a morhpism
getSymbolMap :: Morphism.Morphism -> Map.HashMap Symbol Symbol
getSymbolMap f =
  foldr (\ x -> Map.insert (Symbol x) (Symbol $ applyMap (propMap f) x))
  Map.empty $ Set.toList $ Sign.allItems $ source f

-- | Determines the name of a symbol
getSymbolName :: Symbol -> Id.Id
getSymbolName = symName

symbolToRaw :: Symbol -> Symbol
symbolToRaw = id

idToRaw :: Id.Id -> Symbol
idToRaw mid = Symbol {symName = mid}

-- | Checks two symbols on equality
matches :: Symbol -> Symbol -> Bool
matches s1 s2 = s1 == s2

-- | Adds a symbol to a signature
addSymbToSign :: Sign.Sign -> Symbol -> Result Sign.Sign
addSymbToSign sig symb = Result [] $ Just $
  if Sign.isSeqMark $ symName symb
  then sig { Sign.sequenceMarkers =
                    Set.insert (symName symb) $ Sign.sequenceMarkers sig
           }
  else sig { Sign.discourseNames =
                    Set.insert (symName symb) $ Sign.discourseNames sig
           }

-- | Returns a string classifying the symbol as name or sequence marker
symKind :: Symbol -> String
symKind s = if Sign.isSeqMark $ symName s then symKindSeqMark else symKindName

symKindName :: String
symKindName = "Name"

symKindSeqMark :: String
symKindSeqMark = "SequenceMarker"
