{- |
Module      :  ./SoftFOL/Morphism.hs
Description :  Symbol related functions for SoftFOL.
Copyright   :  (c) Klaus Luettich, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Functions for symbols of SoftFOL.
-}

module SoftFOL.Morphism (symOf, symsOfTerm, symbolToId) where

import SoftFOL.Sign

import Common.Id

import qualified Data.Set as Set
import qualified Data.HashMap.Lazy as Map
import Data.Monoid

symOf :: Sign -> Set.Set SFSymbol
symOf sig =
    let opSymbs = Set.unions $ map toOpSymb $ Map.toList $ funcMap sig
        predSymbs = Set.unions $ map toPredSymb $ Map.toList $ predMap sig
        sortSymbs = Set.map toSortSymb $ Set.fromList $ Map.keys $ sortMap sig
    in Set.unions [opSymbs, predSymbs, sortSymbs]

toOpSymb :: (SPIdentifier, Set.Set ([SPIdentifier], SPIdentifier))
         -> Set.Set SFSymbol
toOpSymb (ident, ts) = Set.map toSymb ts
    where toSymb (args, res) =
             SFSymbol { sym_ident = ident
                      , sym_type = SFOpType args res}

toPredSymb :: (SPIdentifier, Set.Set [SPIdentifier]) -> Set.Set SFSymbol
toPredSymb (ident, ts) = Set.map toSymb ts
    where toSymb args =
             SFSymbol { sym_ident = ident
                      , sym_type = SFPredType args}

toSortSymb :: SPIdentifier -> SFSymbol
toSortSymb ident = SFSymbol { sym_ident = ident
                            , sym_type = SFSortType}

symbolToId :: SFSymbol -> Id
symbolToId = simpleIdToId . sym_ident


idsOfTerm :: SPTerm -> Set.Set SPIdentifier
idsOfTerm (SPQuantTerm _ vars f) = idsOfTerm f Set.\\ mconcat (map idsOfTerm vars)
idsOfTerm (SPComplexTerm (SPCustomSymbol s) args) = 
  Set.insert s $ mconcat $ map idsOfTerm args
idsOfTerm (SPComplexTerm _ args) = mconcat $ map idsOfTerm args

symsOfTerm :: Sign -> SPTerm -> Set.Set SFSymbol
symsOfTerm sig t = Set.filter in_term sig_syms
   where sig_syms = symOf sig
         term_ids = idsOfTerm t
         in_term sy = sym_ident sy `Set.member` term_ids 

