{- |
Module      :  $Header$
Description :  OWL Morphisms
Copyright   :  (c) Dominik Luecke, 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Morphisms for OWL
-}

module OWL.Morphism
  ( OWLMorphism (..)
  , isOWLInclusion
  , inclOWLMorphism
  , legalMor
  , composeMor
  , cogeneratedSign
  , matchesSym
  , statSymbItems
  , statSymbMapItems
  ) where

import OWL.AS
import OWL.Print ()
import OWL.Sign
import OWL.StaticAnalysis

import Common.DocUtils
import Common.Doc
import Common.Keywords
import Common.Result
import Common.Lib.State

import Control.Monad
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

data OWLMorphism = OWLMorphism
  { osource :: Sign
  , otarget :: Sign
  , mmaps :: Map.Map EntityType (Map.Map URI URI)
  } deriving (Show, Eq, Ord)

inclOWLMorphism :: Sign -> Sign -> OWLMorphism
inclOWLMorphism s t = OWLMorphism
 { osource = s
 , otarget = t
 , mmaps = Map.empty }

isOWLInclusion :: OWLMorphism -> Bool
isOWLInclusion m = Map.null (mmaps m) && isSubSign (osource m) (otarget m)

convertMMaps :: Map.Map EntityType (Map.Map URI URI) -> Map.Map Entity URI
convertMMaps = Map.foldWithKey
  (\ k e m -> Map.union m $ Map.mapKeys (Entity k) e) Map.empty

-- also print the symbol mappings
instance Pretty OWLMorphism where
  pretty m = specBraces (pretty $ osource m)
    $+$ text mapsTo <+> specBraces (pretty $ otarget m)

-- check if mapped symbols are in the target signature, too
legalMor :: OWLMorphism -> Bool
legalMor m = let mm = convertMMaps $ mmaps m in
  Set.isSubsetOf (Map.keysSet mm) $ symOf $ osource m

-- composition currently only works for inclusions
composeMor :: OWLMorphism -> OWLMorphism -> Result OWLMorphism
composeMor m = return . inclOWLMorphism (osource m) . otarget

cogeneratedSign :: Set.Set Entity -> Sign -> Result OWLMorphism
cogeneratedSign s sign =
  let sig2 = execState (mapM_ (modEntity Set.delete) $ Set.toList s) sign
  in if isSubSign sig2 sign then return $ inclOWLMorphism sig2 sign else
         fail "non OWL subsignatures for cogeneratedSign"

matchesSym :: Entity -> RawSymb -> Bool
matchesSym e@(Entity _ u) r = case r of
  ASymbol s -> s == e
  AnUri s -> s == u

statSymbItems :: [SymbItems] -> [RawSymb]
statSymbItems = concatMap
  $ \ (SymbItems m us) -> case m of
               Nothing -> map AnUri us
               Just ty -> map (ASymbol . Entity ty) us

statSymbMapItems :: [SymbMapItems] -> Result (Map.Map RawSymb RawSymb)
statSymbMapItems =
  foldM (\ m (s, t) -> case Map.lookup s m of
    Nothing -> return $ Map.insert s t m
    Just u -> case (u, t) of
      (AnUri su, ASymbol (Entity _ tu)) | su == tu ->
        return $ Map.insert s t m
      (ASymbol (Entity _ su), AnUri tu) | su == tu ->
        return m
      _ -> if u == t then return m else
        fail $ "differently mapped symbol: " ++ showDoc s "\nmapped to "
             ++ showDoc u " and " ++ showDoc t "")
  Map.empty
  . (concatMap
    $ \ (SymbMapItems m us) ->
      let ps = map (\ (u, v) -> (u, fromMaybe u v)) us in
      case m of
        Nothing -> map (\ (s, t) -> (AnUri s, AnUri t)) ps
        Just ty -> let mS = ASymbol . Entity ty in
                   map (\ (s, t) -> (mS s, mS t)) ps)
