{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./TPTP/Morphism.hs
Description :  Symbol-related functions for TPTP.
Copyright   :  (c) Eugen Kuksa University of Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional
Portability :  non-portable (imports Logic)

Symbol-related functions for TPTP.
-}

module TPTP.Morphism ( Morphism
                     , symbolsOfSign
                     , symbolToId
                     ) where

import TPTP.AS
import TPTP.Sign as Sign

import Common.DefaultMorphism
import Common.Id
import qualified Data.HashMap.Strict as Map

import Data.Maybe
import qualified Data.HashSet as Set

type Morphism = DefaultMorphism Sign

mkSymbol :: Token -> SymbolType -> Symbol
mkSymbol i t = Symbol { symbolId = i , symbolType = t }

gatherTHFSymbols :: SymbolType -> THFTypeDeclarationMap -> Set.HashSet Symbol
gatherTHFSymbols symType = Set.map fromJust . Set.filter isJust .
  Set.map (\ x -> mkSymbolFromTHFType x symType) . Set.fromList . Map.keys
  where
    mkSymbolFromTHFType :: THFTypeable -> SymbolType -> Maybe Symbol
    mkSymbolFromTHFType x t = case x of
      THFTypeConstant c -> Just $ Symbol { symbolId = c, symbolType = t }
      THFTypeFormula _ -> Nothing

mkSymbolFromTFFType :: Untyped_atom -> SymbolType -> Symbol
mkSymbolFromTFFType x t = case x of
  UA_constant c -> Symbol { symbolId = c, symbolType = t }
  UA_system c -> Symbol { symbolId = c, symbolType = t }

mkToken :: Show a => a -> Token
mkToken = mkSimpleId . show

symbolsOfSign :: Sign -> Set.HashSet Symbol
symbolsOfSign sign = Set.unions [
    Set.map (\ x -> mkSymbol x Sign.Constant) $ constantSet sign
  , Set.map (\ x -> mkSymbol (mkToken x) Sign.Number) $ numberSet sign
  , Set.map (\ x -> mkSymbol x Sign.Proposition) $ propositionSet sign
  , gatherTHFSymbols Sign.TypeConstant $ thfTypeConstantMap sign
  , Set.map (\ x -> mkSymbolFromTFFType x Sign.TypeConstant) $ Set.fromList $ Map.keys $ tffTypeConstantMap sign
  , gatherTHFSymbols Sign.Predicate $ thfPredicateMap sign
  , Set.map (\ x -> mkSymbolFromTFFType x Sign.Predicate) $ Set.fromList $ Map.keys $ tffPredicateMap sign
  , Set.map (\ x -> mkSymbol x Sign.Predicate) $ Set.fromList $ Map.keys $ fofPredicateMap sign
  , gatherTHFSymbols Sign.Function $ thfTypeFunctorMap sign
  , Set.map (\ x -> mkSymbolFromTFFType x Sign.Function) $ Set.fromList $ Map.keys $ tffTypeFunctorMap sign
  ]

symbolToId :: Symbol -> Id
symbolToId = simpleIdToId . symbolId
