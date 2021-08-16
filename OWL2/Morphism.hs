{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./OWL2/Morphism.hs
Description :  OWL Morphisms
Copyright   :  (c) Dominik Luecke, 2008, Felix Gabriel Mance, 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Morphisms for OWL
-}

module OWL2.Morphism where

import Common.IRI
import qualified OWL2.AS as AS
--import OWL2.MS
import OWL2.Sign
import OWL2.ManchesterPrint ()
import OWL2.Symbols
import OWL2.Function

import Common.DocUtils
import Common.Doc
import Common.Result
import Common.Utils (composeMap)
import Common.Lib.State (execState)
import Common.Lib.MapSet (setToMap)
import Common.Id(nullRange)

import Control.Monad

import Data.Data
import Data.List (stripPrefix)
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

data OWLMorphism = OWLMorphism
  { osource :: Sign
  , otarget :: Sign
  , mmaps :: MorphMap
  , pmap :: StringMap
  } deriving (Show, Eq, Ord, Typeable, Data)

inclOWLMorphism :: Sign -> Sign -> OWLMorphism
inclOWLMorphism s t = OWLMorphism
 { osource = s
 , otarget = t
 , pmap = Map.empty
 , mmaps = Map.empty }

isOWLInclusion :: OWLMorphism -> Bool
isOWLInclusion m = Map.null (pmap m)
  && Map.null (mmaps m) && isSubSign (osource m) (otarget m)

symMap :: MorphMap -> Map.Map AS.Entity AS.Entity
symMap = Map.mapWithKey (\ (AS.Entity lb ty _) -> AS.Entity lb ty)

inducedElems :: MorphMap -> [AS.Entity]
inducedElems = Map.elems . symMap

inducedSign :: MorphMap -> StringMap -> Sign -> Sign
inducedSign m t s =
    let new = execState (do
            mapM_ (modEntity Set.delete) $ Map.keys m
            mapM_ (modEntity Set.insert) $ inducedElems m) s
    in function Rename (StringMap t) new

inducedPref :: String -> String -> Sign -> (MorphMap, StringMap)
    -> Result (MorphMap, StringMap)
inducedPref v u sig (m, t) =
    let pm = prefixMap sig
    in if Set.member v $ Map.keysSet pm
         then if u == v then return (m, t) else return (m, Map.insert v u t)
        else
          plain_error (Map.empty, Map.empty) ("unknown symbol: " ++ showDoc v "\nin signature:\n" ++ showDoc sig "") nullRange

 
inducedFromMor :: Map.Map RawSymb RawSymb -> Sign -> Result OWLMorphism
inducedFromMor rm sig = do
  let syms = symOf sig
  (mm, tm) <- foldM (\ (m, t) p -> case p of
        (ASymbol s@(AS.Entity _ _ v), ASymbol (AS.Entity _ _ u)) ->
            if Set.member s syms
            then return $ if u == v then (m, t) else (Map.insert s u m, t)
            else fail $ "unknown symbol: " ++ showDoc s "\n" ++ shows sig ""
        (AnUri v, AnUri u) -> case filter (`Set.member` syms)
          $ map (`AS.mkEntity` v) AS.entityTypes of
          [] -> let v2 = showIRICompact v
                    u2 = showIRICompact u
                in inducedPref v2 u2 sig (m, t)
          l -> return $ if u == v then (m, t) else
                            (foldr (`Map.insert` u) m l, t)
        (APrefix v, APrefix u) -> inducedPref v u sig (m, t)
        _ -> error "OWL2.Morphism.inducedFromMor") (Map.empty, Map.empty)
                        $ Map.toList rm
  return OWLMorphism
    { osource = sig
    , otarget = inducedSign mm tm sig
    , pmap = tm
    , mmaps = mm }

symMapOf :: OWLMorphism -> Map.Map AS.Entity AS.Entity
symMapOf mor = Map.union (symMap $ mmaps mor) $ setToMap $ symOf $ osource mor

instance Pretty OWLMorphism where
  pretty m = let
    s = osource m
    srcD = specBraces $ space <> pretty s
    t = otarget m
    in fsep $ if isOWLInclusion m then
           if isSubSign t s then
              [text "identity morphism over", srcD]
           else
             [ text "inclusion morphism of"
             , srcD
             , text "extended with"
             , pretty $ Set.difference (symOf t) $ symOf s ]
       else
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
  let nm = Set.fold (\ s@(AS.Entity _ ty u) -> let
            t = getIri ty u $ mmaps m1
            r = getIri ty t $ mmaps m2
            in if r == u then id else Map.insert s r) Map.empty
           . symOf $ osource m1
  in return m1
     { otarget = otarget m2
     , pmap = composeMap (prefixMap $ osource m1) (pmap m1) $ pmap m2
     , mmaps = nm }

cogeneratedSign :: Set.Set AS.Entity -> Sign -> Result OWLMorphism
cogeneratedSign s sign =
  let sig2 = execState (mapM_ (modEntity Set.delete) $ Set.toList s) sign
  in if isSubSign sig2 sign then return $ inclOWLMorphism sig2 sign else
         fail "non OWL2 subsignatures for (co)generatedSign"

generatedSign :: Set.Set AS.Entity -> Sign -> Result OWLMorphism
generatedSign s sign = cogeneratedSign (Set.difference (symOf sign) s) sign

matchesSym :: AS.Entity -> RawSymb -> Bool
matchesSym e@(AS.Entity _ _ u) r = case r of
       ASymbol s -> s == e
       AnUri s -> s == u  -- expandedIRI s == expandedIRI u 
                || case
         stripPrefix (reverse $ show $ iriPath s) (reverse $ show $ iriPath u) of
           Just (c : _) | null (prefixName s) -> elem c "/#"
           _ -> False
       APrefix p -> p == prefixName u

statSymbItems :: Sign -> [SymbItems] -> [RawSymb]
statSymbItems sig = map (function Expand . StringMap $ prefixMap sig)
  . concatMap
  (\ (SymbItems m us) -> case m of
               AnyEntity -> map AnUri us
               EntityType ty -> map (ASymbol . AS.mkEntity ty) us
               PrefixO -> map (APrefix . showIRI) us)

statSymbMapItems :: Sign -> Maybe Sign -> [SymbMapItems]
  -> Result (Map.Map RawSymb RawSymb)
statSymbMapItems sig mtsig =
  fmap (Map.fromList . map (\ (r1, r2) ->
        let f = function Expand . StringMap . prefixMap
            f1 = f sig
            f2 = f $ fromMaybe sig mtsig
        in (f1 r1, f2 r2)) . Map.toList)
  . foldM (\ m (s, t) -> case Map.lookup s m of
    Nothing -> return $ Map.insert s t m
    Just u -> case (u, t) of
      (AnUri su, ASymbol (AS.Entity _ _ tu)) | su == tu ->
        return $ Map.insert s t m
      (ASymbol (AS.Entity _ _ su), AnUri tu) | su == tu -> return m
      (AnUri su, APrefix tu) | showIRICompact su == tu ->
        return $ Map.insert s t m
      (APrefix su, AnUri tu) | su == showIRICompact tu -> return m
      _ -> if u == t then return m else
        fail $ "differently mapped symbol: " ++ showDoc s "\nmapped to "
             ++ showDoc u " and " ++ showDoc t "")
  Map.empty
  . concatMap (\ (SymbMapItems m us) ->
      let ps = map (\ (u, v) -> (u, fromMaybe u v)) us in
      case m of
        AnyEntity -> map (\ (s, t) -> (AnUri s, AnUri t)) ps
        EntityType ty ->
            let mS = ASymbol . AS.mkEntity ty
            in map (\ (s, t) -> (mS s, mS t)) ps
        PrefixO ->
            map (\ (s, t) -> (APrefix (showIRICompact s), APrefix $ showIRICompact t)) ps)

mapSen :: OWLMorphism -> AS.Axiom -> Result AS.Axiom
mapSen m a = do
    let new = function Rename (MorphMap $ mmaps m) a
    return $ function Rename (StringMap $ pmap m) new

morphismUnion :: OWLMorphism -> OWLMorphism -> Result OWLMorphism
morphismUnion mor1 mor2 = do
 let ssig1 = osource mor1
     tsig1 = otarget mor1
     ssig2 = osource mor2
     tsig2 = otarget mor2
     ssig = addSign ssig1 ssig2
     tsig = addSign tsig1 tsig2
     m1 = mmaps mor1
     m2 = mmaps mor2
     intM = Map.intersection m1 m2
     pairs = filter (\(a,b) -> a /= b)
             $ map (\x -> (Map.findWithDefault (error "1") x m1, 
                           Map.findWithDefault (error "2") x m2)) 
             $ Map.keys intM
 case pairs of 
  [] -> 
    return $  OWLMorphism {
                 osource = ssig,
                 otarget = tsig,
                 mmaps = Map.union m1 m2,
                 pmap = Map.union (pmap mor1) $ pmap mor2}
  _ -> fail $ "can't unite morphisms:" ++ show pairs
