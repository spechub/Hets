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
import qualified OWL2.AS as AS
import Common.IRI

import Common.SetColimit
import Common.Lib.Graph

import Data.Graph.Inductive.Graph as Graph
import qualified Data.Map as Map

signColimit :: Gr Sign (Int, OWLMorphism) ->
               (Sign, Map.Map Int OWLMorphism)
signColimit graph = let
   conGraph = emap (getEntityTypeMap AS.Class) $ nmap concepts graph
   dataGraph = emap (getEntityTypeMap AS.Datatype) $ nmap datatypes graph
   indGraph = emap (getEntityTypeMap AS.NamedIndividual) $ nmap individuals graph
   objGraph = emap (getEntityTypeMap AS.ObjectProperty) $
              nmap objectProperties graph
   dataPropGraph = emap (getEntityTypeMap AS.DataProperty) $
               nmap dataProperties graph
   annPropGraph = emap (getEntityTypeMap AS.AnnotationProperty) $
               nmap annotationRoles graph
   _prefixGraph = emap getPrefixMap
                    $ nmap (Map.keysSet . toQName . prefixMap) graph
   (con, funC) = addIntToSymbols $ computeColimitSet conGraph
   (dat, funD) = addIntToSymbols $ computeColimitSet dataGraph
   (ind, funI) = addIntToSymbols $ computeColimitSet indGraph
   (obj, funO) = addIntToSymbols $ computeColimitSet objGraph
   (dp, funDP) = addIntToSymbols $ computeColimitSet dataPropGraph
   (ap, funAP) = addIntToSymbols $ computeColimitSet annPropGraph
   -- (pf, funP) = addIntToSymbols $ computeColimitSet prefixGraph
   morFun i = foldl Map.union Map.empty
               [ setEntityTypeMap AS.Class $
                   Map.findWithDefault (error "maps") i funC,
                 setEntityTypeMap AS.Datatype $
                   Map.findWithDefault (error "maps") i funD,
                 setEntityTypeMap AS.NamedIndividual $
                   Map.findWithDefault (error "maps") i funI,
                 setEntityTypeMap AS.ObjectProperty $
                   Map.findWithDefault (error "maps") i funO,
                 setEntityTypeMap AS.DataProperty $
                   Map.findWithDefault (error "maps") i funDP,
                 setEntityTypeMap AS.AnnotationProperty $
                   Map.findWithDefault (error "maps") i funAP
                ]
   morMaps = Map.fromAscList $
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
   colimMor = Map.fromAscList $
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

getEntityTypeMap :: AS.EntityType -> (Int, OWLMorphism)
                    -> (Int, Map.Map IRI IRI)
getEntityTypeMap e (i, phi) = let
 f = Map.filterWithKey
      (\ (AS.Entity _ x _) _ -> x == e) $ mmaps phi
 in (i, Map.fromList $
    map (\ (AS.Entity _ _ x, y) -> (x, y)) $
    Map.toAscList f)

setEntityTypeMap :: AS.EntityType -> Map.Map IRI IRI
                    -> Map.Map AS.Entity IRI
setEntityTypeMap = Map.mapKeys . AS.mkEntity

getPrefixMap :: (Int, OWLMorphism) -> (Int, Map.Map IRI IRI)
getPrefixMap (i, phi) = let
    f = pmap phi
    in (i, Map.fromList $
        map (\ (x, y) -> (mkIRI x, mkIRI y)) $
            Map.toAscList f)

toQName :: AS.PrefixMap -> Map.Map IRI String
toQName pm = Map.fromList $ map (\ (p, s) -> (mkIRI p, s)) $ Map.toList pm
