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
  , inducedFromMor
  ) where

import OWL.AS
import OWL.Print ()
import OWL.Sign
import OWL.StaticAnalysis

import Common.DocUtils
import Common.Doc
import Common.Result
import Common.Lib.State

import Control.Monad
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

data OWLMorphism = OWLMorphism
  { osource :: Sign
  , otarget :: Sign
  , mmaps :: Map.Map Entity URI
  } deriving (Show, Eq, Ord)

inclOWLMorphism :: Sign -> Sign -> OWLMorphism
inclOWLMorphism s t = OWLMorphism
 { osource = s
 , otarget = t
 , mmaps = Map.empty }

isOWLInclusion :: OWLMorphism -> Bool
isOWLInclusion m = Map.null (mmaps m) && isSubSign (osource m) (otarget m)

inducedElems :: Map.Map Entity URI -> [Entity]
inducedElems = Map.elems . Map.mapWithKey (\ (Entity ty _) u -> Entity ty u)

inducedSign :: Map.Map Entity URI -> Sign -> Sign
inducedSign m = execState $ do
    mapM_ (modEntity Set.delete) $ Map.keys m
    mapM_ (modEntity Set.insert) $ inducedElems m

inducedFromMor :: Map.Map RawSymb RawSymb -> Sign -> Result OWLMorphism
inducedFromMor rm sig = do
  let syms = symOf sig
  mm <- foldM (\ m p -> case p of
        (ASymbol s@(Entity _ v), ASymbol (Entity _ u)) ->
            if Set.member s syms
            then return $ if u == v then m else Map.insert s u m
            else fail $ "unknown symbol: " ++ showDoc s ""
        (AnUri v, AnUri u) -> case filter (flip Set.member syms)
          $ map (\ ty -> Entity ty v) entityTypes of
          [] -> fail $ "unknown symbol: " ++ showDoc v ""
          l -> return $ if u == v then m else foldr (flip Map.insert u) m l
        _ -> error "OWL.Morphism.inducedFromMor") Map.empty $ Map.toList rm
  return OWLMorphism
    { osource = sig
    , otarget = inducedSign mm sig
    , mmaps = mm }

instance Pretty OWLMorphism where
  pretty m = let
    s = osource m
    srcD = specBraces $ space <> pretty s
    t = otarget m
    in if isOWLInclusion m then
           if isSubSign t s then
              fsep [text "identity morphism over", srcD]
           else fsep
             [ text "inclusion morphism of"
             , srcD
             , text "extended with"
             , pretty $ Set.difference (symOf t) $ symOf s ]
       else fsep
         [ pretty $ mmaps m
         , colon <+> srcD, mapsto <+> specBraces (space <> pretty t) ]

legalMor :: OWLMorphism -> Bool
legalMor m = let mm = mmaps m in
  Set.isSubsetOf (Map.keysSet mm) (symOf $ osource m)
  && Set.isSubsetOf (Set.fromList $ inducedElems mm) (symOf $ otarget m)

composeMor :: OWLMorphism -> OWLMorphism -> Result OWLMorphism
composeMor m1 m2 =
  let nm = Set.fold (\ s@(Entity ty u) -> let
            t = case Map.lookup s $ mmaps m1 of
              Nothing -> u
              Just v -> v
            r = case Map.lookup (Entity ty t) $ mmaps m2 of
              Nothing -> t
              Just w -> w
            in if r == u then id else Map.insert s r) Map.empty
           $ symOf $ osource m1
  in return m1
     { otarget = otarget m2
     , mmaps = nm }

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


