{- |
Module      :  $Header$
Description :  Symbol related functions for SoftFOL.
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic)

Functions for symbols of SoftFOL.
-}


module SoftFOL.Morphism (symOf,symbolToId,morphismToSymbolMap) where

import SoftFOL.Sign

import Common.Id
import Common.DefaultMorphism

import qualified Data.Set as Set
import qualified Data.Map as Map

symOf :: Sign -> Set.Set SFSymbol
symOf sig = 
    let opSymbs = Set.unions $ map toOpSymb $ Map.toList $ funcMap sig
        predSymbs = Set.unions $ map toPredSymb $ Map.toList $ predMap sig
        sortSymbs = Set.map toSortSymb $ Map.keysSet $ sortMap sig
    in Set.unions [opSymbs,predSymbs,sortSymbs]

toOpSymb :: (SPIdentifier,Set.Set([SPIdentifier], SPIdentifier)) 
         -> Set.Set SFSymbol
toOpSymb (ident,ts) = Set.map toSymb ts
    where toSymb (args,res) =
             SFSymbol { sym_ident = ident
                      , sym_type = SFOpType args res}

toPredSymb :: (SPIdentifier,Set.Set [SPIdentifier]) 
           -> Set.Set SFSymbol
toPredSymb (ident,ts) = Set.map toSymb ts
    where toSymb args =
             SFSymbol { sym_ident = ident
                      , sym_type = SFPredType args}

toSortSymb :: SPIdentifier -> SFSymbol
toSortSymb ident = SFSymbol { sym_ident = ident
                            , sym_type = SFSortType}

type SymbolMap = Map.Map SFSymbol SFSymbol

morphismToSymbolMap :: DefaultMorphism Sign -> SymbolMap
morphismToSymbolMap (MkMorphism src trg) =
    let sortSymMap = mkSortSymMap (sortMap src) (sortMap trg)
        opSymMap = mkFuncSymMap sortSymMap (funcMap src) (funcMap trg)
        predSymMap = mkPredSymMap sortSymMap (predMap src) (predMap trg)
    in foldr Map.union sortSymMap [opSymMap,predSymMap]

mkSortSymMap :: SortMap -> SortMap -> SymbolMap
mkSortSymMap src trg =
    Map.empty

mkFuncSymMap :: SymbolMap -> FuncMap -> FuncMap -> SymbolMap
mkFuncSymMap sortMap src trg =
    Map.empty

mkPredSymMap :: SymbolMap -> PredMap -> PredMap -> SymbolMap
mkPredSymMap sortMap src trg =
    Map.empty

symbolToId :: SFSymbol -> Id
symbolToId = mkId . (:[]) . mkSimpleId . sym_ident
    
