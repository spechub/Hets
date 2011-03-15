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

module Static.FromXml where

import Static.DevGraph
import Static.GTheory

import Common.Result (Result (..))
import Common.ExtSign (ExtSign (..))

import Logic.ExtSign (ext_empty_signature)
import Logic.Logic (AnyLogic (..), inclusion)
import Logic.Prover (noSens)
import Logic.Grothendieck {- (LogicGraph (..), G_morphism (..), GMorphism,
                           gEmbed, startSigId, startMorId) -}

import qualified Data.Map as Map (lookup)
import Data.List (partition, isInfixOf)

import Text.XML.Light


-- | for faster access, some elements attributes are stored alongside
-- as a String
type NamedNode = (String,Element)
type NamedLink = ((String,String),Element)


-- | main function; receives an logicGraph and an initial DGraph, then adds
-- all nodes and edges from an xml element into the DGraph 
fromXml :: LogicGraph -> DGraph -> Element -> DGraph
fromXml lg dg el = case Map.lookup (currentLogic lg) (logics lg) of
  Nothing ->
    error "FromXML.fromXML: current logic was not found in logicMap"
  Just (Logic lid) -> let
    emptyTheory = G_theory lid (ext_empty_signature lid)
                    startSigId noSens startThId
    nodes = extractNodeElements el
    links = extractLinkElements el
    (dg', depNodes) = initialiseNodes dg emptyTheory nodes links
    in iterateLinks dg' depNodes links


-- | All nodes are taken from the xml-element. Then, the name-attribute is
-- looked up and stored alongside the node for easy access. Nodes with no names
-- are ignored (and should never occur).
extractNodeElements :: Element -> [NamedNode]
extractNodeElements = foldr f [] . findChildren (unqual "DGNode") where
  f e r = case findAttr (unqual "name") e of
            Just name -> (name, e) : r
            Nothing -> r


-- | All links are taken from the xml-element. The links have then to be 
-- filtered so that only definition links are considered. Then, the source and
-- target attributes are looked up and stored alongside the link access. Links
-- with source or target information missing are irgnored.
extractLinkElements :: Element -> [NamedLink]
extractLinkElements = foldr f [] . filter isDef . 
                    findChildren (unqual "DGLink") where
  f e r = case findAttr (unqual "source") e of
            Just src -> case findAttr (unqual "target") e of
              Just trg -> ((src, trg), e) : r
              Nothing -> r
            Nothing -> r
  isDef e = case findChild (unqual "Type") e of
              Just tp -> isInfixOf "Def" $ strContent tp
              Nothing -> False


-- |  All nodes that do not have dependencies via the links are processed at 
-- the beginning and written into the DGraph. The remaining nodes are returned
-- as well for further processing.
initialiseNodes :: DGraph -> G_theory -> [NamedNode] -> [NamedLink] 
                -> (DGraph,[NamedNode])
initialiseNodes dg gt nodes links = let 
  targets = map (snd . fst) links
  -- all nodes that are not targeted by any links are considered independent
  (dep, indep) = partition ((`elem` targets) . fst) nodes
  dg' = foldl insertNodeDG dg $ map (mkDGNodeLab gt) indep
  in (dg',dep)


-- | Writes a single Node into the DGraph
insertNodeDG :: DGraph -> DGNodeLab -> DGraph
insertNodeDG dg lbl = let n = getNewNodeDG dg in
  insLNodeDG (n,lbl) dg


-- TODO: get LEdge label!
insertEdgeDG :: NamedLink -> DGraph -> DGraph
insertEdgeDG e@((src,trg),l) dg = undefined -- let (EdgeId i) = getNewEdgeId dg in
--  insLEdgeDG (i, globDefLink (getEdgeMorphism dg e) SeeTarget) dg

-- TODO: kill constraint: double occurence of sign does not work!
getEdgeMorphism :: DGraph -> NamedLink -> GMorphism
getEdgeMorphism dg ((src,trg),_) = case signOf $ theoryOfNode src dg of
  G_sign lid (ExtSign s0 _) _ -> --case signOf $ theoryOfNode trg dg of
    --G_sign _ (ExtSign s1 _) _ -> 
       case maybeResult $ inclusion lid s0 s0 of -- s0 s1 of
         Just mor -> gEmbed (G_morphism lid mor startMorId) 
         Nothing -> error "FromXml.getEdgeMorphism"


theoryOfNode :: String -> DGraph -> G_theory
theoryOfNode n dg = case lookupNodeByName n dg of
  [(_,lbl)] -> dgn_theory lbl
  _ -> error "FromXml.theoryOfNode: NodeName was not found in DGraph"


-- | This is the main loop. In every step, all links are extracted which source
-- has already been processed. Then, for each of these links, the target node
-- is calculated and stored using the sources G_theory.
-- The function is called again with the remaining links and additional nodes
-- (stored in DGraph) until the list of links reaches null.
iterateLinks :: DGraph -> [NamedNode] -> [NamedLink] -> DGraph
iterateLinks dg _ [] = dg
iterateLinks dg nodes links = let (cur,lftL) = splitLinks dg links
                                  (dg',lftN) = processNodes nodes cur dg
  in if null cur then error 
      "FromXML.iterateLinks: remaining links cannot be processed"
    else iterateLinks dg' lftN lftL


-- | Help function for iterateNodes. For every link, the target node is created
-- and stored in DGraph. Then the link is stored in DGraph.
-- Returns updated DGraph and the list of nodes that have not been captured.
processNodes :: [NamedNode] -> [(G_theory,NamedLink)] -> DGraph 
             -> (DGraph,[NamedNode])
processNodes nodes [] dg = (dg,nodes)
processNodes nodes ((th,l@((_,trg),_)):ls) dg = 
  case partition ((== trg) . fst) nodes of
    ([o],r) -> processNodes r ls $ insertEdgeDG l 
            $ insertNodeDG dg (mkDGNodeLab th o)
    _ -> error "fromXML.processNodes: link has no or multiple targets"


-- | Help function for iterateNodes. Given a list of links, it partitions the
-- links depending on if their source has been processed. Then stores the
-- source-nodes G_theory alongside for easy access.
splitLinks :: DGraph -> [NamedLink] -> ([(G_theory,NamedLink)],[NamedLink])
splitLinks dg = foldr (\l@((src,_),_) (r,r') -> case lookupNodeByName src dg of
    [(_,lbl)] -> ((dgn_theory lbl, l):r,r')
    [] -> (r,l:r') 
    _ -> error "FromXML.splitLinks: found multiple nodes for one NodeName" 
  ) ([],[])


-- | Generates a new DGNodeLab with a startoff-G_theory and an Element
mkDGNodeLab :: G_theory -> NamedNode -> DGNodeLab
mkDGNodeLab gt (name, el) = let
  (response,message) = extendByBasicSpec (extractSpecString el) gt -- TODO test string extraction!
  in case response of
    Failure _ -> error $ "FromXML.mkDGNodeLab: "++message
    Success gt' _ symbs _ -> 
      newNodeLab (parseNodeName name) (DGBasicSpec Nothing symbs) gt'


-- TODO: String extraction does not work. fix it.
extractSpecString :: Element -> String
extractSpecString el = let decl = findChildren (unqual "Declarations") el in
  unlines $ map strContent $ concat $ map elChildren decl


