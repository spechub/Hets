{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./HPL/Symbol.hs
Description :  Symbols of hybrid propositional logic
Copyright   :  (c) Mihai Codescu, IMAR, 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mscodescu@gmail.com
Stability   :  experimental
Portability :  portable

Definition of symbols for hybrid propositional logic
-}


module HPL.Symbol
    (
     Symbol (..)           -- Symbol type
    , SymKind (..)
    , pretty               -- pretty printing for Symbols
    , symOf                -- Extracts the symbols out of a signature
    , symKindStr           -- the kind of a symbol as a string
    , getSymbolMap         -- Determines the symbol map
    , getSymbolName        -- Determines the name of a symbol
    --, idToRaw              -- Creates a raw symbol
    , symbolToRaw          -- Convert symbol to raw symbol
    , matches              -- does a symbol match a raw symbol?
    , applySymMap          -- application function for symbol maps
    ) where

import Propositional.ATC_Propositional ()

import qualified Common.Id as Id
import Common.Doc
import Common.DocUtils

import Data.Data
import qualified Data.Set as Set
import qualified Data.Map as Map

import qualified Propositional.Sign as PSign
import qualified Propositional.Morphism as PMorphism
import qualified HPL.Sign as HSign
import qualified HPL.Morphism as HMorphism

data SymKind = PropKind | NomKind
       deriving (Show, Eq, Ord, Typeable, Data)

-- | Datatype for symbols
data Symbol = Symbol { symName :: Id.Id
                        , symKind :: SymKind}
            deriving (Show, Eq, Ord, Typeable, Data)

instance Id.GetRange Symbol where
    getRange = Id.getRange . symName

instance Pretty Symbol where
    pretty = printSymbol

printSymbol :: Symbol -> Doc
printSymbol x = pretty $ symName x

symKindStr :: Symbol -> String
symKindStr (Symbol _ PropKind) = "prop"
symKindStr (Symbol _ NomKind)  = "state"

-- | Extraction of symbols from a signature
symOf :: HSign.HSign -> Set.Set Symbol
symOf sig = 
  let 
    pSymSet = Set.fold 
              (\ y -> Set.insert Symbol {symName = y, symKind = PropKind})
              Set.empty $
              PSign.items $ HSign.propSig sig
  in Set.fold 
              (\ y -> Set.insert Symbol {symName = y, symKind = NomKind})
              pSymSet $
              HSign.noms sig

-- | Determines the symbol map of a morhpism
getSymbolMap :: HMorphism.HMorphism -> Map.Map Symbol Symbol
getSymbolMap f =
 let 
  m = foldr 
       (\ x -> Map.insert (Symbol x PropKind) 
                          (Symbol (PMorphism.applyMap 
                                     (HMorphism.propMap f) x) 
                           PropKind)
       )
       Map.empty $
       Set.toList $ PSign.items $ HSign.propSig $ HMorphism.source f
 in foldr 
       (\ x -> Map.insert (Symbol x NomKind) 
                          (Symbol (PMorphism.applyMap 
                                     (HMorphism.nomMap f) x) 
                           NomKind)
       )
       m $
       Set.toList $ HSign.noms $ HMorphism.source f

-- | Determines the name of a symbol
getSymbolName :: Symbol -> Id.Id
getSymbolName = symName

-- | make a raw_symbol
idToRawProp :: Id.Id -> Symbol
idToRawProp mid = Symbol {symName = mid, symKind = PropKind}

idToRawNom :: Id.Id -> Symbol
idToRawNom mid = Symbol {symName = mid, symKind = NomKind}

-- | convert to raw symbol
symbolToRaw :: Symbol -> Symbol
symbolToRaw = id

-- | does a smybol match a raw symbol?
matches :: Symbol -> Symbol -> Bool
matches s1 s2 = s1 == s2

-- | application function for Symbol Maps
applySymMap :: Map.Map Symbol Symbol -> Symbol -> Symbol
applySymMap smap idt = Map.findWithDefault idt idt smap

