{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./Propositional/Symbol.hs
Description :  Symbols of propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Definition of symbols for propositional logic
-}


module NeSyPatterns.Symbol
    (
     Symbol (..)           -- Symbol type
    , pretty               -- pretty printing for Symbols
    , symOf                -- Extracts the symbols out of a signature
    , getSymbolMap         -- Determines the symbol map
    , getSymbolName        -- Determines the name of a symbol
    , idToRaw              -- Creates a raw symbol
    , symbolToRaw          -- Convert symbol to raw symbol
    , matches              -- does a symbol match a raw symbol?
    , applySymMap          -- application function for symbol maps
    ) where

import Common.IRI
import qualified Common.Id as Id
import Common.Doc
import Common.DocUtils

import Data.Data
import qualified Data.Set as Set
import qualified Data.Map as Map

import qualified NeSyPatterns.Sign as Sign
import NeSyPatterns.Morphism as Morphism

import NeSyPatterns.Sign (ResolvedNode)

-- | Datatype for symbols
newtype Symbol = Symbol { node :: ResolvedNode }
    deriving (Show, Eq, Ord, Typeable, Data)

instance Id.GetRange Symbol where
    getRange = Id.getRange . node

instance Pretty Symbol where
    pretty = printSymbol

printSymbol :: Symbol -> Doc
printSymbol = pretty . node

-- | Extraction of symbols from a signature
symOf :: Sign.Sign -> Set.Set Symbol
symOf = Set.map Symbol . Sign.nodes

-- | Determines the symbol map of a morhpism
getSymbolMap :: Morphism.Morphism -> Map.Map Symbol Symbol
getSymbolMap f = 
  foldr
    (\n -> Map.insert (Symbol n) (Symbol $ Morphism.applyMap (Morphism.nodeMap f) n))
    (Map.empty :: Map.Map Symbol Symbol)
    (Sign.nodes (source f))

-- | Determines the name of a symbol
getSymbolName :: Symbol -> Id.Id
getSymbolName (Symbol ( Sign.ResolvedNode o i _)) = Id.appendId (uriToCaslId o) (uriToCaslId i)

-- | make a raw_symbol
idToRaw :: Id.Id -> Symbol
idToRaw mid = case Id.getPlainTokenList mid of
  [o, i] -> case (parseIRI $ show o, parseIRI $ show i) of 
      (Just o', Just i') -> Symbol $ Sign.ResolvedNode o' i' (Id.posOfId mid)
      _ -> error "NeSyPatterns.Symbol.idToRaw: Invalid iri"
  _ -> error "NeSyPatterns.Symbol.idToRaw: Invalid number of tokens"

-- | convert to raw symbol
symbolToRaw :: Symbol -> Symbol
symbolToRaw = id

-- | does a smybol match a raw symbol?
matches :: Symbol -> Symbol -> Bool
matches n1 n2 = let 
    a = node n1
    b = node n2
    o = Sign.resolvedOTerm
    i = Sign.resolvedNeSyId
    in
    o a == o b && i a == i b

-- | application function for Symbol Maps
applySymMap :: Map.Map Symbol Symbol -> Symbol -> Symbol
applySymMap smap idt = Map.findWithDefault idt idt smap
