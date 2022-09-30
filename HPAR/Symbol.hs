{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./HPAR/Symbol.hs
Description :  Morphisms in HPAR
Copyright   :  (c) R. Diaconescu, IMAR, 2018
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mscodescu@gmail.cm
Stability   :  experimental
Portability :  portable

  Definition of symbols for HPAR
  
-}

module HPAR.Symbol where

import qualified CASL.Sign as CSign
import qualified HPAR.Sign as HSign
import Common.Id
import Common.Doc
import Common.DocUtils
import Data.Data
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified CASL.Morphism as CMor

-- symbols

data HSymbol = BSymbol CSign.Symbol
             | HSymb Id HKind
 deriving (Show, Eq, Ord, Typeable, Data) 

data HKind = NKind | MKind Int 
 deriving (Show, Eq, Ord, Typeable, Data)

instance Pretty HSymbol where
 pretty (BSymbol s) = pretty s
 pretty (HSymb i _) = pretty i

instance GetRange HSymbol where
    getRange (BSymbol s) = getRange s
    getRange (HSymb i _ ) = getRange i
    rangeSpan (BSymbol s) = rangeSpan s
    rangeSpan (HSymb i _ ) = rangeSpan i

-- raw symbols

data HRawSymbol = ASymbol HSymbol 
                | AKindedSymb HKind Id -- does this suffice?
     deriving (Show, Eq, Ord, Typeable, Data)

symOf :: HSign.HSign -> [Set.Set HSymbol]
symOf hsign = 
 let 
   bSyms = CMor.symOf $ HSign.baseSig hsign
   nSyms = HSign.noms hsign
   mSyms = HSign.mods hsign
 in [Set.map (\x -> HSymb x NKind) nSyms] ++
    [Set.fromList $ map (\(m,i) -> HSymb m (MKind i)) $ Map.toList mSyms] ++
    map (\ss -> Set.map (\s -> BSymbol s) ss) bSyms

symName :: HSymbol -> Id
symName (BSymbol s) = CSign.symName s
symName (HSymb i _) = i
    
