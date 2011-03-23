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
import Data.Maybe (fromMaybe)

import Text.XML.Light


-- | for faster access, some elements attributes are stored alongside
-- as a String
type NamedNode = (String,Element)

data NamedLink = Link { src :: String
                      , trg :: String
                      , srcNode :: Maybe (LNode DGNodeLab)
                      , element :: Element }

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
    (defLinks, thmLinks) = extractLinkElements el
    (dg0, depNodes) = initialiseNodes dg emptyTheory nodes defLinks
    dg1 = insertNodesAndDefLinks lg dg0 depNodes defLinks
    dgFinal = dg1 --insertThmLinks lg dg1 thmLinks
    in computeDGraphTheories Map.empty dgFinal


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


-- | All nodes are taken from the xml-element. Then, the name-attribute is
-- looked up and stored alongside the node for easy access. Nodes with no names
-- are ignored (and should never occur).
extractNodeElements :: Element -> [NamedNode]
extractNodeElements = foldr f [] . findChildren (unqual "DGNode") where
  f e r = case getAttrVal "name" e of
            Just name -> (name, e) : r
            Nothing -> r


-- | All links are taken from the xml-element. The source and target attributes
-- are looked up and stored alongside the link access. Links with source or 
-- target information missing are irgnored.
-- Finally the links are partitioned dependent on whether they are definition
-- or theorem links.
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


-- |  All nodes that do not have dependencies via the links are processed at 
-- the beginning and written into the DGraph. The remaining nodes are returned
-- as well for further processing.
initialiseNodes :: DGraph -> G_theory -> [NamedNode] -> [NamedLink] 
                -> (DGraph,[NamedNode])
initialiseNodes dg gt nodes links = let 
  targets = map trg links
  -- all nodes that are not targeted by any links are considered independent
  (dep, indep) = partition ((`elem` targets) . fst) nodes
  dg' = foldr (insertNodeDG gt) dg indep
  in (dg',dep)


-- | This is the main loop. In every step, all links are extracted which source
-- has already been processed. Then, for each of these links, the target node
-- is calculated and stored using the sources G_theory (If a node is targeted
-- by more than one link, refer to insMultTrg).
-- The function is called again with the remaining links and additional nodes
-- (stored in DGraph) until the list of links reaches null.
insertNodesAndDefLinks :: LogicGraph -> DGraph -> [NamedNode] -> [NamedLink]
                       -> DGraph
insertNodesAndDefLinks _ dg _ [] = dg
insertNodesAndDefLinks lg dg nodes links = let
  (cur,lftL) = splitLinks dg links
  (dg',lftN) = processNodes lg nodes cur dg
  in if (not . null) cur then insertNodesAndDefLinks lg dg' lftN lftL
     else error $
      "FromXml.insertNodesAndDefLinks: remaining links cannot be processed!\n"
        ++ printLinks lftL


-- | Help function for iterateNodes. Given a list of links, it partitions the
-- links depending on if their source has been processed.
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


-- | Help function for insertNodesAndDefLinks. 
-- For every Node, all Links targeting this Node are collected. Then the Node
-- is processed depending on if none, one or multiple Links are targeting it.
-- Returns updated DGraph and the list of nodes that have not been captured.
processNodes :: LogicGraph -> [NamedNode] -> [NamedLink] -> DGraph
             -> (DGraph,[NamedNode])
processNodes _ nodes [] dg = (dg,nodes)
processNodes _ [] links _ = error $ 
    "FromXml.processNodes: remaining links targets cannot be found!\n"
      ++ printLinks links
processNodes lg (x@(name,_):xs) links dg = 
  case partition ((== name) . trg) links of
    -- Case #1: Only one Link is targetting the current Node.
    -- The Node can be inserted using the links source-theory.
    ([l],ls) -> processNodes lg xs ls $ insertDefLinkDG lg l
       $ insertNodeDG (deleteSentences (thOfSrc l)) x dg
    -- Case #2: None of the current links are targetting the Node.
    -- Append Node and contiue with the rest.
    ([],_) -> let (dg',xs') = processNodes lg xs links dg
      in (dg',x:xs')
    -- Case #3: Multiple Links are targetting the Node.
    -- A merged Signature must be created, see insMultTrg..
    (sameTrg,ls) -> processNodes lg xs ls $ insMultTrg lg x sameTrg dg


-- | When a new node is created, the old nodes sentences have to be removed
-- from the derived G_theory.
deleteSentences :: G_theory -> G_theory
deleteSentences gt = case signOf gt of
  G_sign lid sign sId -> noSensGTheory lid sign sId


-- | returns the G_theory of a links source node
thOfSrc :: NamedLink -> G_theory
thOfSrc l = case srcNode l of
  Nothing -> error "FromXml.thOfSrc: Links sourceNode was not found!"
  Just (_,lbl) -> dgn_theory lbl


-- | if multiple links target one node, a G_theory must be calculated using
-- the signature of all ingoing links via gSigUnion.
insMultTrg :: LogicGraph -> NamedNode -> [NamedLink] -> DGraph -> DGraph
insMultTrg lg x links dg = let
  signs = map (signOf . thOfSrc) links
  res = propagateErrors "FromXml.insMultTrg:" $ gsigManyUnion lg signs
  in case res of
    G_sign lid sign sId -> let 
      gt = noSensGTheory lid sign sId in
      foldr (insertDefLinkDG lg) (insertNodeDG gt x dg) links


-- | After all other Elements are inserted, this function inserts the
-- theorem links into the DGraph
insertThmLinks :: LogicGraph -> DGraph -> [NamedLink] -> DGraph
insertThmLinks lg dg = foldl (insertThmLinkDG lg) dg


-- | Inserts a Theorem Link into the DGraph.
insertThmLinkDG :: LogicGraph -> DGraph -> NamedLink -> DGraph
insertThmLinkDG lg dg l = let
  n1 = fromMaybe (error "FromXml.insertThmLinkDG") $ getNodeByName (src l) dg
  n2 = fromMaybe (error "FromXml.insertThmLinkDG") $ getNodeByName (trg l) dg
  lType = case findChild (unqual "Type") (element l) of
    Nothing -> error 
      "FromXml.insertThmLinks: Links type field is missing!"
    Just tp -> if isInfixOf "Global" $ strContent tp
      then globalThm else localThm
  in insertLink lg dg n1 n2 lType


-- | Inserts a Definition Link into the DGraph.
-- ( Currently, all definition links are considered to be global ).
insertDefLinkDG :: LogicGraph -> NamedLink -> DGraph -> DGraph
insertDefLinkDG lg l dg = let
  n1 = fromMaybe (error "FromXml.insertDefLinkDG") $ srcNode l
  n2 = fromMaybe (error "FromXml.insertDefLinkDG") $ getNodeByName (trg l) dg
  in insertLink lg dg n1 n2 globalDef


-- | Inserts a new edge into the DGraph.
-- This function is the reason why the logicGraph is passed through, because
-- it implements Grothendieck.ginclusion for getting the links GMorphism.
insertLink :: LogicGraph -> DGraph -> LNode DGNodeLab -> LNode DGNodeLab
           -> DGLinkType -> DGraph
insertLink lg dg (i,lbl1) (j,lbl2) lType = let
  gsign = signOf . dgn_theory
  morph = propagateErrors "FromXml.insertLink:" $
    ginclusion lg (gsign lbl1) (gsign lbl2)
  in snd $ insLEdgeDG (i, j, defDGLink morph lType SeeTarget) dg


-- | A links symbol mapping must be deduced to a specific string in order
-- to derive the correct signature from it.
getSymbolMapStr :: NamedLink -> String
getSymbolMapStr l = case deepSearch [unqual "map"] (element l) of
  [] -> ""
  ms -> let mkStr = intercalate " |-> " . map strContent . elChildren
     in intercalate ", " $ map mkStr ms


-- | A Node is looked up via its name in the DGraph. Returns the node only
-- if one single node is found for the respective name, otherwise an error
-- is thrown.
getNodeByName :: String -> DGraph -> Maybe (LNode DGNodeLab)
getNodeByName s dg = case lookupNodeByName s dg of
  [n] -> Just n
  [] -> Nothing
  _ -> error $ 
    "FromXml.getNodeByName: ambiguous occurence for " ++ s ++ "!"

 
-- | Writes a single Node into the DGraph
insertNodeDG :: G_theory -> NamedNode -> DGraph -> DGraph
insertNodeDG gt ele dg = let lbl = mkDGNodeLab gt ele
                             n = getNewNodeDG dg
  in insLNodeDG (n,lbl) dg


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

