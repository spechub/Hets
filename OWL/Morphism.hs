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
  ( OWL_Morphism
  , cogeneratedSign
  , matchesSym
  , statSymbItems
  , statSymbMapItems
  ) where


import OWL.AS
import OWL.Print ()
import OWL.Sign
import OWL.StaticAnalysis

import Common.DefaultMorphism
import Common.DocUtils
import Common.Result
import Common.Lib.State

import Control.Monad
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

type OWL_Morphism = DefaultMorphism Sign

cogeneratedSign :: Set.Set Entity -> Sign -> Result OWL_Morphism
cogeneratedSign s sign =
  let sig2 = execState (mapM_ (modEntity Set.delete) $ Set.toList s) sign
  in if isSubSign sig2 sign then defaultInclusion sig2 sign else
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
      let ps = map (\ (u, v) -> (u, maybe u id v)) us in
      case m of
        Nothing -> map (\ (s, t) -> (AnUri s, AnUri t)) ps
        Just ty -> let mS = ASymbol . Entity ty in
                   map (\ (s, t) -> (mS s, mS t)) ps)
