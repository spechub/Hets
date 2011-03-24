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

import Static.ComputeTheory (computeDGraphTheories)
import Static.DevGraph
import Static.GTheory

import Common.LibName (LibName(..), emptyLibName)
import Common.Result (propagateErrors)
import Common.XUpdate (getAttrVal)

import Comorphisms.LogicGraph (logicGraph)

import Logic.ExtSign (ext_empty_signature)
import Logic.Logic (AnyLogic (..))
import Logic.Prover (noSens)
import Logic.Grothendieck

import qualified Data.Map as Map (lookup, insert, empty)
import Data.List (partition, intercalate, isInfixOf)
import Data.Graph.Inductive.Graph (LNode)
import qualified Data.Graph.Inductive.Graph as Graph (Node)
import Data.Maybe (fromMaybe)

import Text.XML.Light


-- | for faster access, some elements attributes are stored alongside
-- as a String
type NamedNode = (String,Element)

data NamedLink = Link { src :: String
                      , trg :: String
                      , srcNode :: Maybe (LNode DGNodeLab)
                      , element :: Element }


-- | main function; receives a FilePath and calls fromXml upon that path,
-- using an empty DGraph and initial LogicGraph.
readDGXml :: FilePath -> IO(Maybe (LibName,LibEnv))
readDGXml path = do
  xml' <- readFile path
  case parseXMLDoc xml' of
    Nothing -> do
      putStrLn "FromXml.readDGXml: failed to parse XML file"
      return Nothing
    Just xml -> case getAttrVal "filename" xml of
      Nothing -> do
        putStrLn "FromXml.readDGXml: DGraphs name attribute is missing!"
        return Nothing
      Just nm -> let
        dg = fromXml logicGraph emptyDG xml
        ln = emptyLibName nm
        le = Map.insert ln dg Map.empty
        in return $ Just (ln,le)


-- | main function; receives a logicGraph, an initial DGraph and an xml
-- element, then adds all nodes and edges from the element into the DGraph 
fromXml :: LogicGraph -> DGraph -> Element -> DGraph
fromXml lg dg el = case Map.lookup (currentLogic lg) (logics lg) of
  Nothing ->
    error "FromXml.FromXml: current logic was not found in logicMap"
  Just (Logic lid) -> let
    emptyTheory = G_theory lid (ext_empty_signature lid)
                    startSigId noSens startThId
    nodes = extractNodeElements el
    (defLinks, thmLinks) = extractLinkElements el
    (dg', depNodes) = initialiseNodes emptyTheory nodes defLinks dg
    in (computeDGraphTheories Map.empty . insertThmLinks lg thmLinks .
      insertNodesAndDefLinks lg depNodes defLinks) dg'


-- | All nodes are taken from the xml-element. Then, the name-attribute is
-- looked up and stored alongside the node for easy access. Nodes with no names
-- are ignored.
extractNodeElements :: Element -> [NamedNode]
extractNodeElements = foldr f [] . findChildren (unqual "DGNode") where
  f e r = case getAttrVal "name" e of
            Just name -> (name, e) : r
            Nothing -> r


-- | All links are taken from the xml-element and stored alongside their source
-- and target information. The links are then partitioned depending on if they
-- are theorem or definition links.
extractLinkElements :: Element -> ([NamedLink],[NamedLink])
extractLinkElements = partition isDef . foldr f [] . 
                    findChildren (unqual "DGLink") where
  f e r = case getAttrVal "source" e of
            Just sr -> case getAttrVal "target" e of
              Just tr -> (Link sr tr Nothing e) : r
              Nothing -> r
            Nothing -> r
  isDef l = case findChild (unqual "Type") (element l) of
              Just tp -> isInfixOf "Def" $ strContent tp
              Nothing -> error 
                "FromXml.extractLinkElements: Links type field is missing!"


-- | All nodes that do not have dependencies via the links are processed at the
-- beginning and written into the DGraph. Returns the resulting DGraph and the
-- list of nodes that have not been stored (i.e. have dependencies). 
initialiseNodes :: G_theory -> [NamedNode] -> [NamedLink] -> DGraph 
                -> (DGraph,[NamedNode])
initialiseNodes gt nodes links dg = let 
  targets = map trg links
  -- all nodes that are not targeted by any links are considered independent
  (dep, indep) = partition ((`elem` targets) . fst) nodes
  dg' = foldr (insertNode gt) dg indep
  in (dg',dep)


-- | main loop: in every step, all links are collected of which the source node
-- has been written into DGraph already. Upon these, further nodes are written
-- in each step until the list of remaining links reaches null.
insertNodesAndDefLinks :: LogicGraph -> [NamedNode] -> [NamedLink] -> DGraph
                       -> DGraph
insertNodesAndDefLinks _ _ [] dg = dg
insertNodesAndDefLinks lg nodes links dg = let
  (cur,lftL) = splitLinks dg links
  (dg',lftN) = iterateNodes lg nodes cur dg
  in if (not . null) cur then insertNodesAndDefLinks lg lftN lftL dg'
     else error $
      "FromXml.insertNodesAndDefLinks: remaining links cannot be processed!\n"
        ++ printLinks lftL


insertThmLinks :: LogicGraph -> [NamedLink] -> DGraph -> DGraph
insertThmLinks = undefined


-- | Help function for insertNodesAndDefLinks. Given a list of links, it
-- partitions the links depending on if their source has been processed.
splitLinks :: DGraph -> [NamedLink] -> ([NamedLink],[NamedLink])
splitLinks dg = killMultTrg . foldr partition' ([],[]) where
  partition' l (r,r') = case getNodeByName (src l) dg of
    Nothing -> (r, l:r')
    dgn -> (l { srcNode = dgn }:r, r')
  -- if a link targets a node that is also targeted by another link which
  -- cannot be processed at this step, the first link is also appended.
  killMultTrg (hasSrc,noSrc) = let noSrcTrgs = map trg noSrc in
    foldr (\l (r,r') -> if elem (trg l) noSrcTrgs
      then (r, l:r') else (l:r, r')) ([],noSrc) hasSrc


-- | returns a String representation of a list of links showing their
-- source and target nodes.
printLinks :: [NamedLink] -> String
printLinks = let show' l = src l ++ " -> " ++ trg l in
  unlines . (map show')


-- | Help function for insertNodesAndDefLinks. Given the currently processable
-- links and the total of remaining nodes, it stores all processable elements
-- into the DGraph. Returns the updated DGraph and a list of remaining nodes.
iterateNodes :: LogicGraph -> [NamedNode] -> [NamedLink] -> DGraph
             -> (DGraph,[NamedNode])
iterateNodes _ nodes [] dg = (dg,nodes)
iterateNodes _ [] links _ = error $ 
  "FromXml.iterateNodes: remaining links targets cannot be found!\n"
    ++ printLinks links
iterateNodes lg (x@(name,_):xs) links dg = 
  case partition ((== name) . trg) links of
    -- Case #1: Only one Link is targetting the current Node.
    ([l],ls) -> iterateNodes lg xs ls $ insSinglTrg lg x l dg
    -- Case #2: None of the current links are targetting the Node.
    ([],_) -> let (dg',xs') = iterateNodes lg xs links dg
      in (dg',x:xs')
    -- Case #3: Multiple Links are targetting the Node.
    (sameTrg,ls) -> iterateNodes lg xs ls $ insMultTrg lg x sameTrg dg


insSinglTrg :: LogicGraph -> NamedNode -> NamedLink -> DGraph -> DGraph
insSinglTrg lg x l dg = let
  (i,morph) = prepareLink lg l
  (j,dg') = insertNode2 morph x dg
  in insertLink i j globalDef morph dg'


insMultTrg :: LogicGraph -> NamedNode -> [NamedLink] -> DGraph -> DGraph
insMultTrg lg x ls dg = let
  (h:t) = map (prepareLink lg) ls
  morph = foldr comp' (snd h) t where
    comp' (_,m1) m2 = propagateErrors "" $ compInclusion lg m1 m2
  (j,dg') = insertNode2 morph x dg
  insert' (i,m) = insertLink i j globalDef m
  in foldr insert' dg' $ (h:t)


prepareLink :: LogicGraph -> NamedLink -> (Graph.Node, GMorphism)
prepareLink lg l = let
  (i,lbl) = fromMaybe (error "") $ srcNode l
  sign1 = signOf $ dgn_theory lbl
  morph = getLinkMorphism lg sign1 l
  in (i,morph)


getLinkMorphism :: LogicGraph -> G_sign -> NamedLink -> GMorphism
getLinkMorphism lg s1 l = case findChild (unqual "GMorphism") (element l) of
    Just mor -> let
      nm = fromMaybe (error "FromXml.getLinkMorphism: No name attribute") 
         $ getAttrVal "name" mor
      symbs = parseSymbolMap $ findChildren (unqual "map") mor
      in propagateErrors "" $ getGMorphism lg s1 nm symbs
    Nothing -> error "FromXml.getLinkMorphism: Link has no Morphism!" 

  
parseSymbolMap :: [Element] -> String
parseSymbolMap = intercalate ", " . map mkStr where
  mkStr = intercalate " |-> " . map strContent . elChildren


insertLink :: Graph.Node -> Graph.Node -> DGLinkType -> GMorphism -> DGraph -> DGraph
insertLink i j lType morph = 
  insEdgeDG (i,j, defDGLink morph lType SeeTarget)


insertNode2 :: GMorphism -> NamedNode -> DGraph -> (Graph.Node, DGraph)
insertNode2 gm x dg = let g_th = undefined -- TODO: get proper G_theory from GMorphism
                          lbl = mkDGNodeLab g_th x
                          n = getNewNodeDG dg
  in (n, insLNodeDG (n,lbl) dg)


insertNode :: G_theory -> NamedNode -> DGraph -> DGraph
insertNode gt x dg = let lbl = mkDGNodeLab gt x
                         n = getNewNodeDG dg
  in insLNodeDG (n,lbl) dg


-- | A Node is looked up via its name in the DGraph. Returns the node only
-- if one single node is found for the respective name, otherwise an error
-- is thrown.
getNodeByName :: String -> DGraph -> Maybe (LNode DGNodeLab)
getNodeByName s dg = case lookupNodeByName s dg of
  [n] -> Just n
  [] -> Nothing
  _ -> error $ 
    "FromXml.getNodeByName: ambiguous occurence for " ++ s ++ "!"

 
-- | Generates a new DGNodeLab with a startoff-G_theory and an Element
mkDGNodeLab :: G_theory -> NamedNode -> DGNodeLab
mkDGNodeLab gt (name, el) = case extractSpecString el of
  "" -> newNodeLab (parseNodeName name) DGBasic gt
  specs -> let
    (response,message) = extendByBasicSpec specs gt
    in case response of
      Failure _ -> error $ "FromXml.mkDGNodeLab: " ++ message
      Success gt' _ symbs _ -> 
        newNodeLab (parseNodeName name) (DGBasicSpec Nothing symbs) gt'


-- | Extracts a String including all Axioms, Theorems and Symbols from the
-- xml-Element (supposedly for one Node only).
extractSpecString :: Element -> String
extractSpecString e = let
  specs = map unqual ["Axiom","Theorem","Symbol"]
  elems = deepSearch specs e
  in unlines $ map strContent elems


-- | custom xml-search for not only immediate children
deepSearch :: [QName] -> Element -> [Element]
deepSearch names e = filterChildrenName (`elem` names) e ++
  concat (map (deepSearch names) (elChildren e))


