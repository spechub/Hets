{- |
Module      :  $Header$
Description :  OWL Morphisms
Copyright   :  (c) Dominik Luecke, 2008, Felix Gabriel Mance, 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Morphisms for OWL
-}

module OWL2.Morphism where

import OWL2.AS
import OWL2.MS
import OWL2.Sign
import OWL2.ManchesterPrint ()
import OWL2.StaticAnalysis
import OWL2.Symbols
import OWL2.Function

import Common.DocUtils
import Common.Doc
import Common.Result
import Common.Utils (composeMap)
import Common.Lib.State (execState)
import Common.Lib.MapSet (setToMap)

import Control.Monad
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

data OWLMorphism = OWLMorphism
  { osource :: Sign
  , otarget :: Sign
  , mmaps :: MorphMap
  , pmap :: StringMap
  } deriving (Show, Eq, Ord)

inclOWLMorphism :: Sign -> Sign -> OWLMorphism
inclOWLMorphism s t = OWLMorphism
 { osource = s
 , otarget = t
 , pmap = Map.empty
 , mmaps = Map.empty }

isOWLInclusion :: OWLMorphism -> Bool
isOWLInclusion m = Map.null (pmap m)
  && Map.null (mmaps m) && isSubSign (osource m) (otarget m)

symMap :: MorphMap -> Map.Map Entity Entity
symMap = Map.mapWithKey (\ (Entity ty _) -> Entity ty)

inducedElems :: MorphMap -> [Entity]
inducedElems = Map.elems . symMap

inducedSign :: MorphMap -> StringMap -> Sign -> Sign
inducedSign m t s =
    let new = execState (do
            mapM_ (modEntity Set.delete) $ Map.keys m
            mapM_ (modEntity Set.insert) $ inducedElems m) s
    in function Rename (StringMap t) new

inducedPref :: String -> String -> Sign -> (MorphMap, StringMap)
    -> (MorphMap, StringMap)
inducedPref v u sig (m, t) =
    let pm = prefixMap sig
    in if Set.member v $ Map.keysSet pm
         then if u == v then (m, t) else (m, Map.insert v u t)
        else error $ "unknown symbol: " ++ showDoc v "\n" ++ shows sig ""

inducedFromMor :: Map.Map RawSymb RawSymb -> Sign -> Result OWLMorphism
inducedFromMor rm sig = do
  let syms = symOf sig
  (mm, tm) <- foldM (\ (m, t) p -> case p of
        (ASymbol s@(Entity _ v), ASymbol (Entity _ u)) ->
            if Set.member s syms
            then return $ if u == v then (m, t) else (Map.insert s u m, t)
            else fail $ "unknown symbol: " ++ showDoc s "\n" ++ shows sig ""
        (AnUri v, AnUri u) -> case filter (`Set.member` syms)
          $ map (`Entity` v) entityTypes of
          [] -> let v2 = showQU v
                    u2 = showQU u
                in return $ inducedPref v2 u2 sig (m, t)
          l -> return $ if u == v then (m, t) else
                            (foldr (`Map.insert` u) m l, t)
        (APrefix v, APrefix u) -> return $ inducedPref v u sig (m, t)
        _ -> error "OWL2.Morphism.inducedFromMor") (Map.empty, Map.empty)
                        $ Map.toList rm
  return OWLMorphism
    { osource = sig
    , otarget = inducedSign mm tm sig
    , pmap = tm
    , mmaps = mm }

symMapOf :: OWLMorphism -> Map.Map Entity Entity
symMapOf mor = Map.union (symMap $ mmaps mor) $ setToMap $ symOf $ osource mor

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
         , pretty $ pmap m
         , colon <+> srcD, mapsto <+> specBraces (space <> pretty t) ]

legalMor :: OWLMorphism -> Result ()
legalMor m = let mm = mmaps m in unless
  (Set.isSubsetOf (Map.keysSet mm) (symOf $ osource m)
  && Set.isSubsetOf (Set.fromList $ inducedElems mm) (symOf $ otarget m))
        $ fail "illegal OWL2 morphism"

composeMor :: OWLMorphism -> OWLMorphism -> Result OWLMorphism
composeMor m1 m2 =
  let nm = Set.fold (\ s@(Entity ty u) -> let
            t = getIri ty u $ mmaps m1
            r = getIri ty t $ mmaps m2
            in if r == u then id else Map.insert s r) Map.empty
           . symOf $ osource m1
  in return m1
     { otarget = otarget m2
     , pmap = composeMap (prefixMap $ osource m1) (pmap m1) $ pmap m2
     , mmaps = nm }

cogeneratedSign :: Set.Set Entity -> Sign -> Result OWLMorphism
cogeneratedSign s sign =
  let sig2 = execState (mapM_ (modEntity Set.delete) $ Set.toList s) sign
  in if isSubSign sig2 sign then return $ inclOWLMorphism sig2 sign else
         fail "non OWL2 subsignatures for (co)generatedSign"

generatedSign :: Set.Set Entity -> Sign -> Result OWLMorphism
generatedSign s sign = cogeneratedSign (Set.difference (symOf sign) s) sign

matchesSym :: Entity -> RawSymb -> Bool
matchesSym e@(Entity _ u) r = case r of
  ASymbol s -> s == e
  AnUri s -> s == u || namePrefix u == localPart s && null (namePrefix s)
  APrefix p -> p == namePrefix u

statSymbItems :: [SymbItems] -> [RawSymb]
statSymbItems = concatMap
  $ \ (SymbItems m us) -> case m of
               AnyEntity -> map AnUri us
               EntityType ty -> map (ASymbol . Entity ty) us
               Prefix -> map (APrefix . showQN) us

statSymbMapItems :: [SymbMapItems] -> Result (Map.Map RawSymb RawSymb)
statSymbMapItems =
  foldM (\ m (s, t) -> case Map.lookup s m of
    Nothing -> return $ Map.insert s t m
    Just u -> case (u, t) of
      (AnUri su, ASymbol (Entity _ tu)) | su == tu ->
        return $ Map.insert s t m
      (ASymbol (Entity _ su), AnUri tu) | su == tu -> return m
      (AnUri su, APrefix tu) | showQU su == tu ->
        return $ Map.insert s t m
      (APrefix su, AnUri tu) | su == showQU tu -> return m
      _ -> if u == t then return m else
        fail $ "differently mapped symbol: " ++ showDoc s "\nmapped to "
             ++ showDoc u " and " ++ showDoc t "")
  Map.empty
  . concatMap (\ (SymbMapItems m us) ->
      let ps = map (\ (u, v) -> (u, fromMaybe u v)) us in
      case m of
        AnyEntity -> map (\ (s, t) -> (AnUri s, AnUri t)) ps
        EntityType ty ->
            let mS = ASymbol . Entity ty
            in map (\ (s, t) -> (mS s, mS t)) ps
        Prefix ->
            map (\ (s, t) -> (APrefix (showQU s), APrefix $ showQU t)) ps)

mapSen :: OWLMorphism -> Axiom -> Result Axiom
mapSen m a = do
    let new = function Rename (MorphMap $ mmaps m) a
    return $ function Rename (StringMap $ pmap m) new
