{- |
Module      :  $Header$
Description :  OWL signatures colimits
Copyright   :  (c) Mihai Codescu, and Uni Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  mcodescu@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable

OWL signature colimits, computed component-wise.

-}

module OWL.ColimSign where

import OWL.Sign
import OWL.Morphism
import OWL.AS

import Common.SetColimit
--import Common.Utils (number)
--import qualified Common.Lib.Rel as Rel
import Common.Lib.Graph

import Data.Graph.Inductive.Graph as Graph
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List

signColimit :: Gr Sign (Int,OWLMorphism) ->
               (Sign, Map.Map Int OWLMorphism)
signColimit graph = let
   conGraph = emap (getEntityTypeMap OWLClass) $ nmap concepts graph
   dataGraph = emap (getEntityTypeMap Datatype)$ nmap datatypes graph
   indGraph = emap (getEntityTypeMap Individual) $ nmap individuals graph
   objGraph = emap (getEntityTypeMap ObjectProperty) $
              nmap indValuedRoles graph
   dataPropGraph = emap (getEntityTypeMap DataProperty) $
               nmap dataValuedRoles graph
   (con, funC) = addIntToSymbols $ computeColimitSet conGraph
   (dat, funD) = addIntToSymbols $ computeColimitSet dataGraph
   (ind, funI) = addIntToSymbols $ computeColimitSet indGraph
   (obj, funO) = addIntToSymbols $ computeColimitSet objGraph
   (dp, funDP) = addIntToSymbols $ computeColimitSet dataPropGraph
   oid = nullQName
   morFun i = foldl Map.union Map.empty $
               [ setEntityTypeMap OWLClass $
                   Map.findWithDefault (error "maps") i funC,
                 setEntityTypeMap Datatype $
                   Map.findWithDefault (error "maps") i funD,
                 setEntityTypeMap Individual $
                   Map.findWithDefault (error "maps") i funI,
                 setEntityTypeMap ObjectProperty $
                   Map.findWithDefault (error "maps") i funO,
                 setEntityTypeMap DataProperty $
                   Map.findWithDefault (error "maps") i funDP
                ]
   morMaps = Map.fromAscList $
              map (\x -> (x,morFun x)) $ nodes graph
   ax = Set.empty
        -- foldl Set.union Set.empty $
        --   map (\(i,axSet) -> let
        --            funI = Map.findWithDefault (error "ax") i morMaps
        --                      in
        --            Set.map (mapSignAxiom funI) axSet) $ -- missing!
        --   map (\(i,l)-> (i, axioms l))$ labNodes graph
   nameMap = foldl Map.union Map.empty $
             map (\(_,l)-> namespaceMap l)$ labNodes graph
      -- here it will be a union with clashing symbols renamed
      -- if their corresponding values are not the same
   pCs = foldl Set.union Set.empty $
         map (\(i,pcs) -> Set.map
                         (\x -> Map.findWithDefault (error "errorColimit") x $
                                Map.findWithDefault (error "error i") i funC)
                         pcs ) $
         map (\(i,l)-> (i, primaryConcepts l))$
         labNodes graph
   colimSign = emptySign{
                  ontologyID = oid,
                  concepts = con,
                  primaryConcepts = pCs,
                  datatypes = dat,
                  indValuedRoles = obj,
                  dataValuedRoles = dp,
                  individuals = ind,
                  axioms = ax,
                  namespaceMap = nameMap
                }
   colimMor = Map.fromAscList $
                map (\(i, ssig) -> let
                         mm = Map.findWithDefault (error "mor") i morMaps
                         om = OWLMorphism{
                               osource = ssig,
                               otarget = colimSign,
                               mmaps = mm
                              }
                                   in (i,om)
                     )$ labNodes graph
  in (colimSign, colimMor)

instance SymbolName QName where
 addIntAsSuffix (QN p l b n, i) = QN p (l ++ show i) b n

getEntityTypeMap :: EntityType -> (Int, OWLMorphism)
                    -> (Int,Map.Map QName QName)
getEntityTypeMap e (i,phi) = let
 f = Map.filterWithKey
      (\(Entity x _)_ -> x == e) $ mmaps phi
 in (i,Map.fromList $
    map (\(Entity _ x, y) -> (x,y)) $
    Map.toAscList f)

setEntityTypeMap :: EntityType -> Map.Map QName QName
                    ->  Map.Map Entity QName
setEntityTypeMap e f = Map.mapKeys (\x -> Entity e x) f

