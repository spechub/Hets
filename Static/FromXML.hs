{- |
Module      :  $Header$
Description :  xml input for Hets development graphs
Copyright   :  (c) Simon Ulbricht, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  tekknix@tzi.de
Stability   :  provisional
Portability :  non-portable (DevGraph)

create new or extend a Development Graph in accordance with an XML input
-}

module Static.FromXML where

import Static.DevGraph
import Static.GTheory

import Logic.Logic (AnyLogic (..))
import Logic.Prover (noSens)
import Logic.Grothendieck (LogicGraph (..), startSigId)
import Logic.ExtSign (ext_empty_signature)

--import Common.Consistency

import qualified Data.Map as Map (lookup)
import Data.List (partition)

import Text.XML.Light

mkQName :: String -> QName
mkQName s = QName s Nothing Nothing

type NamedNode = (String,Element)
type NamedLink = ((String,String),Element)

fromXML :: LogicGraph -> DGraph -> Element -> DGraph
fromXML lg dg el = case Map.lookup (currentLogic lg) (logics lg) of
  Nothing -> 
    error "FromXML.fromXML: current logic was not found in logicMap"
  Just (Logic lid) -> let
    emptyTheory = G_theory lid (ext_empty_signature lid)
                    startSigId noSens startThId
    -- extract all nodes and store them with their names in fst field
    nodes :: [NamedNode]
    nodes = map nameNode $ findChildren (mkQName "DGNode") el where
      nameNode e = case findAttr (mkQName "name") e of
                 Just name -> (name, e)
                 Nothing -> error "FromXML.fromXML: node has no name"
    -- extract all links and store tuple of source and target names in fst field
    links :: [NamedLink] -- TODO filter links so only DefLinks are considered
    links = map nameLink $ findChildren (mkQName "DGLink") el where
      nameLink e = case findAttr (mkQName "source") e of
                 Just src -> case findAttr (mkQName "target") e of
                   Just trg -> ((src, trg), e)
                   Nothing -> error "FromXML.fromXML: link has no target"
                 Nothing -> error "FromXML.fromXML: link has no source"
    (dg', depNodes) = insertInitialNodes dg emptyTheory nodes links
    in iterateLinks dg' depNodes links -- TODO use insLEdgeDG

insertInitialNodes :: DGraph -> G_theory -> [NamedNode] -> [NamedLink] -> (DGraph,[NamedNode])
insertInitialNodes dg gt nodes links = let 
  targets = map (snd . fst) links
  -- all nodes that are not targeted by any links are considered independent
  (dep, indep) = partition ((`elem` targets) . fst) nodes
  dg' = foldl insertNodeDG dg $ map (mkDGNodeLab gt) indep
  in (dg',dep)

insertNodeDG :: DGraph -> DGNodeLab -> DGraph
insertNodeDG dg lbl = let n = getNewNodeDG dg in
  insLNodeDG (n,lbl) dg

-- TODO: links have to be inserted as well
iterateLinks :: DGraph -> [NamedNode] -> [NamedLink] -> DGraph
iterateLinks dg nodes links = case links of
  [] -> dg
  ((src,trg),l):ls -> case lookupNodeByName src dg of
       [(_,lbl)] -> case partition ((== trg) .fst) nodes of
         ([o],r) -> iterateLinks (insertNodeDG dg 
                 (mkDGNodeLab (dgn_theory lbl) o)) r $ ls
         _ -> error "FromXML.iterateLinks: links target is missing" 
       [] -> case lookup src nodes of
         Just _ -> iterateLinks dg nodes $ ls ++ [((src,trg),l)]
         Nothing -> error ""
       _ -> error ""

insertEdgeDG :: DGraph -> NamedLink -> DGraph
insertEdgeDG dg ((src,trg),l) = undefined 


mkDGNodeLab :: G_theory -> NamedNode -> DGNodeLab
mkDGNodeLab gt (name, el) = let
  (response,message) = extendByBasicSpec (strContent el) gt -- TODO extract string properly!
  in case response of
    Failure _ -> error $ "FromXML.mkDGNodeLab: "++message
    Success gt' _ symbs _ -> 
      newNodeLab (parseNodeName name) (DGBasicSpec Nothing symbs) gt'

