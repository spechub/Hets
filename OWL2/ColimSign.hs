{- |
Module      :  ./OWL2/ColimSign.hs
Description :  OWL signatures colimits
Copyright   :  (c) Mihai Codescu, and Uni Bremen 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mcodescu@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable

OWL2 signature colimits, computed component-wise.

-}

module OWL2.ColimSign where

import OWL2.Sign
import OWL2.Morphism
import OWL2.AS
import Common.IRI

import Common.SetColimit
import Common.Lib.Graph

import Data.Graph.Inductive.Graph as Graph
import qualified Data.HashMap.Strict as Map
import qualified Data.Set as Set

signColimit :: Gr Sign (Int, OWLMorphism) ->
               (Sign, Map.HashMap Int OWLMorphism)
signColimit graph = let
   conGraph = emap (getEntityTypeMap Class) $ nmap concepts graph
   dataGraph = emap (getEntityTypeMap Datatype) $ nmap datatypes graph
   indGraph = emap (getEntityTypeMap NamedIndividual) $ nmap individuals graph
   objGraph = emap (getEntityTypeMap ObjectProperty) $
              nmap objectProperties graph
   dataPropGraph = emap (getEntityTypeMap DataProperty) $
               nmap dataProperties graph
   annPropGraph = emap (getEntityTypeMap AnnotationProperty) $
               nmap annotationRoles graph
   _prefixGraph = emap getPrefixMap
                    $ nmap (Set.fromList . Map.keys . toQName . prefixMap) graph
   (con, funC) = addIntToSymbols $ computeColimitSet conGraph
   (dat, funD) = addIntToSymbols $ computeColimitSet dataGraph
   (ind, funI) = addIntToSymbols $ computeColimitSet indGraph
   (obj, funO) = addIntToSymbols $ computeColimitSet objGraph
   (dp, funDP) = addIntToSymbols $ computeColimitSet dataPropGraph
   (ap, funAP) = addIntToSymbols $ computeColimitSet annPropGraph
   -- (pf, funP) = addIntToSymbols $ computeColimitSet prefixGraph
   morFun i = foldl Map.union Map.empty
               [ setEntityTypeMap Class $
                   Map.findWithDefault (error "maps") i funC,
                 setEntityTypeMap Datatype $
                   Map.findWithDefault (error "maps") i funD,
                 setEntityTypeMap NamedIndividual $
                   Map.findWithDefault (error "maps") i funI,
                 setEntityTypeMap ObjectProperty $
                   Map.findWithDefault (error "maps") i funO,
                 setEntityTypeMap DataProperty $
                   Map.findWithDefault (error "maps") i funDP,
                 setEntityTypeMap AnnotationProperty $
                   Map.findWithDefault (error "maps") i funAP
                ]
   morMaps = Map.fromList $
              map (\ x -> (x, morFun x)) $ nodes graph

   nameMap = foldl Map.union Map.empty $
             map (\ (_, l) -> prefixMap l) $ labNodes graph
   colimSign = emptySign {
                  concepts = con,
                  datatypes = dat,
                  objectProperties = obj,
                  dataProperties = dp,
                  individuals = ind,
                  annotationRoles = ap,
                  prefixMap = nameMap
                }
   colimMor = Map.fromList $
                map (\ (i, ssig) -> let
                         mm = Map.findWithDefault (error "mor") i morMaps
                         om = OWLMorphism {
                               osource = ssig,
                               otarget = colimSign,
                               mmaps = mm,
                               pmap = Map.empty
                              }
                                   in (i, om)
                     ) $ labNodes graph
  in (colimSign, colimMor)

getEntityTypeMap :: EntityType -> (Int, OWLMorphism)
                    -> (Int, Map.HashMap IRI IRI)
getEntityTypeMap e (i, phi) = let
 f = Map.filterWithKey
      (\ (Entity _ x _) _ -> x == e) $ mmaps phi
 in (i, Map.fromList $
    map (\ (Entity _ _ x, y) -> (x, y)) $
    Map.toList f)

setEntityTypeMap :: EntityType -> Map.HashMap IRI IRI
                    -> Map.HashMap Entity IRI
setEntityTypeMap et f = Map.fromList $ map (\(x,y) -> (mkEntity et x, y)) $ 
                        Map.toList f

getPrefixMap :: (Int, OWLMorphism) -> (Int, Map.HashMap IRI IRI)
getPrefixMap (i, phi) = let
    f = pmap phi
    in (i, Map.fromList $
        map (\ (x, y) -> (mkIRI x, mkIRI y)) $
            Map.toList f)

toQName :: PrefixMap -> Map.HashMap IRI String
toQName pm = Map.fromList $ map (\ (p, s) -> (mkIRI p, s)) $ Map.toList pm
