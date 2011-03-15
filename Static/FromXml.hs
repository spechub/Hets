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
import Logic.Logic (AnyLogic (..))
import Logic.Prover (noSens)
import Logic.Grothendieck 

import qualified Data.Map as Map (lookup)
import Data.List (partition, isInfixOf)
import Data.Graph.Inductive.Graph (LNode)
import Data.Maybe (fromJust)

import Text.XML.Light

--import Debug.Trace

-- | for faster access, some elements attributes are stored alongside
-- as a String
type NamedNode = (String,Element)
type NamedLink = ((String,String),Element)


-- | main function; receives an logicGraph and an initial DGraph, then adds
-- all nodes and edges from an xml element into the DGraph 
fromXml :: LogicGraph -> DGraph -> Element -> DGraph
fromXml lg dg el = case Map.lookup (currentLogic lg) (logics lg) of
  Nothing ->
    error "FromXml.FromXml: current logic was not found in logicMap"
  Just (Logic lid) -> let
    emptyTheory = G_theory lid (ext_empty_signature lid)
                    startSigId noSens startThId
    nodes = extractNodeElements el
    links = extractLinkElements el
    (dg', depNodes) = initialiseNodes dg emptyTheory nodes links
    in iterateLinks lg dg' depNodes links


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


-- | Inserts a new edge into the DGraph and returns the new DGraph.
-- This function is the reason why the logicGraph is passed through, because
-- it implements Grothendieck.ginclusion for getting the links GMorphism.
insertEdgeDG :: NamedLink -> LogicGraph -> DGraph -> DGraph
insertEdgeDG ((src,trg),_) lg dg = let
  (i,lbl1) = fromJust $ getNodeByName src dg
  (j,lbl2) = fromJust $ getNodeByName trg dg
  gsign = signOf . dgn_theory
  resMorph = ginclusion lg (gsign lbl1) (gsign lbl2) 
  morph = case maybeResult resMorph of
    Just m -> m
    Nothing -> error $ show resMorph
  in snd $ insLEdgeDG (i, j, globDefLink morph SeeTarget) dg 


-- | A Node is looked up via its name in the DGraph. Returns the node only
-- if one single node is found for the respective name, otherwise an error
-- is thrown.
getNodeByName :: String -> DGraph -> Maybe (LNode DGNodeLab)
getNodeByName s dg = case lookupNodeByName s dg of
  [n] -> Just n
  [] -> Nothing
  _ -> error $ "FromXml.getNodeByName: ambiguous occurence for " ++ s ++ "!"


-- | This is the main loop. In every step, all links are extracted which source
-- has already been processed. Then, for each of these links, the target node
-- is calculated and stored using the sources G_theory.
-- The function is called again with the remaining links and additional nodes
-- (stored in DGraph) until the list of links reaches null.
iterateLinks :: LogicGraph -> DGraph -> [NamedNode] -> [NamedLink] -> DGraph
iterateLinks _ dg _ [] = dg
iterateLinks lg dg nodes links = let (cur,lftL) = splitLinks dg links
                                     (dg',lftN) = processNodes nodes cur lg dg
  in if null cur then error 
      "FromXml.iterateLinks: remaining links cannot be processed"
    else iterateLinks lg dg' lftN lftL


--TODO: whenever a node is inserted, all links that target this node must be considered too.
--TODO: use gsigUnion to update the G_sign for these links. if one of those links has no source jet,
-- it must not be considered!

-- | Help function for iterateNodes. For every link, the target node is 
-- created and stored in DGraph. Then the link is stored in DGraph.
-- Returns updated DGraph and the list of nodes that have not been captured.
processNodes :: [NamedNode] -> [(G_theory,NamedLink)] -> LogicGraph -> DGraph
             -> (DGraph,[NamedNode])
processNodes nodes [] _ dg = (dg,nodes)
processNodes nodes ((gt,l@((_,trg),_)):ls) lg dg = 
  case partition ((== trg) . fst) nodes of
    ([o],r) -> processNodes r ls lg $ insertEdgeDG l lg
            $ insertNodeDG dg (mkDGNodeLab gt o)
    ([],r) -> case getNodeByName trg dg of
      Just (_,lbl) -> undefined --TODO gsigUnion
      Nothing -> error $
        "FromXml.processNodes: Target <" ++ trg ++ "> was not found!"
    _ -> error $ 
      "FromXml.processNodes: Target <" ++ trg ++ "> was found multiple times!"


-- | Help function for iterateNodes. Given a list of links, it partitions the
-- links depending on if their source has been processed. Then stores the
-- source-nodes G_theory alongside for easy access.
splitLinks :: DGraph -> [NamedLink] -> ([(G_theory,NamedLink)],[NamedLink])
splitLinks dg = killMultTrg . foldr partition' ([],[]) where
  partition' l@((src,_),_) (r,r') = case getNodeByName src dg of
    Just (_,lbl) -> ((dgn_theory lbl, l):r,r')
    Nothing -> (r,l:r')
  -- if a link targets a node that is also targeted by another link which
  -- cannot be processed at this step, the first link is also appended.
  killMultTrg (hasSrc,noSrc) = let noSrcTrgs = map (snd . fst) noSrc in
    foldr (\(gt,l@((_,trg),_)) (r,r') -> if elem trg noSrcTrgs
      then (r,l:r') else ((gt,l):r,r')) ([],noSrc) hasSrc


-- | Generates a new DGNodeLab with a startoff-G_theory and an Element
mkDGNodeLab :: G_theory -> NamedNode -> DGNodeLab
mkDGNodeLab gt (name, el) = case extractSpecString el of
  "" -> newNodeLab (parseNodeName name) DGBasic gt
  specs -> let 
    (response,message) = extendByBasicSpec specs gt
    in case response of
      Failure _ -> error $ "FromXml.mkDGNodeLab: "++message
      Success gt' _ symbs _ -> 
        newNodeLab (parseNodeName name) (DGBasicSpec Nothing symbs) gt'


-- | Extracts a String including all Axioms, Theorems and Symbols from the
-- xml-Element.
extractSpecString :: Element -> String
extractSpecString e = let
  specs = map unqual ["Axiom","Theorem","Symbol"]
  elems = deepSearch specs e
  in unlines $ map strContent elems


-- | custom xml-search not only for immediate children
deepSearch :: [QName] -> Element -> [Element]
deepSearch names e = filterChildrenName (`elem` names) e ++
  concat (map (deepSearch names) (elChildren e))

