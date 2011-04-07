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
import Common.GlobalAnnotations (GlobalAnnos, emptyGlobalAnnos)
import Common.AnalyseAnnos (getGlobalAnnos)

import Comorphisms.LogicGraph (logicGraph)

import Logic.ExtSign (ext_empty_signature)
import Logic.Logic (AnyLogic (..), cod, composeMorphisms)
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
                      , element :: Element }

linkTypeStr :: NamedLink -> String
linkTypeStr (Link _ _ el) = case findChild (unqual "Type") el of
  Nothing -> error "FromXml.linkTypeStr: Links type field is missing!"
  Just tp -> strContent tp


-- | returns a String representation of a list of links showing their
-- source and target nodes.
printLinks :: [NamedLink] -> String
printLinks = let show' l = src l ++ " -> " ++ trg l in
  unlines . (map show')


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
        an = extractGlobalAnnos xml
        dg = fromXml logicGraph emptyDG {globalAnnos = an} xml
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
    in ( computeDGraphTheories Map.empty
       . insertThmLinks lg thmLinks
       . insertNodesAndDefLinks lg depNodes defLinks
       ) dg'


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


-- | Help function for insertNodesAndDefLinks. Given a list of links, it
-- partitions the links depending on if they can be processed in one step.
splitLinks :: DGraph -> [NamedLink] -> ([NamedLink],[NamedLink])
splitLinks dg = killMultTrg . foldr partiSrc ([],[]) where
  partiSrc l (r,r') = case findNodeByName (src l) dg of
    Nothing -> (r, l:r')
    _ -> (l:r, r')
  killMultTrg (hasSrc,noSrc) = let noSrcTrgs = map trg noSrc in
    foldr (\l (r,r') -> if elem (trg l) noSrcTrgs
      then (r, l:r') else (l:r, r')) ([],noSrc) hasSrc


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
    ([],_) -> let (dg',xs') = iterateNodes lg xs links dg
              in (dg',x:xs')
    (lCur,lLft) -> iterateNodes lg xs lLft
                  $ insDefLinks lg x lCur dg

partitionWith :: Eq a => (NamedLink -> a) -> a -> [NamedLink] -> ([NamedLink],[NamedLink])
partitionWith f v ls = partition ((== v) . f) ls

insertThmLinks :: LogicGraph -> [NamedLink] -> DGraph -> DGraph
insertThmLinks _ [] dg = dg
insertThmLinks lg (l:ls) dg = let
  (lCur,lLft) = partitionWith trg (trg l) ls
  gsig = signOf $ dgn_theory $ snd $ fromMaybe (error "FromXml.insertThmLinks(1)")
       $ findNodeByName (trg l) dg
  morph x = let m1 = extractMorphism lg dg x in
    propagateErrors "FromXml.insertThmLinks(2):"
      $ composeMorphisms m1 $ propagateErrors "FromXml.insertThmLinks(3):"
      $ ginclusion lg (cod m1) gsig
  ins' x dgr = insertLink (morph x) globalThm x dgr
  in insertThmLinks lg lLft $ foldr ins' dg (l:lCur)


insDefLinks :: LogicGraph -> NamedNode -> [NamedLink] -> DGraph -> DGraph
insDefLinks _ _ [] dg = dg
insDefLinks lg trgNd links dg = let
  mrs = map (extractMorphism lg dg) links
  gsig1 = propagateErrors "FromXml.insDefLinks(1):" $
           gsigManyUnion lg $ map cod mrs
  gt = case gsig1 of
         G_sign lid sg sId -> noSensGTheory lid sg sId
  dg' = insertNode gt trgNd dg
  gsig2 = signOf $ dgn_theory $ snd $ fromMaybe (error "FromXml.insDefLinks(2)")
       $ findNodeByName (fst trgNd) dg'
  mr' m = propagateErrors "FromXml.insDefLinks(3):"
            $ composeMorphisms m $ propagateErrors "FromXml.insDefLinks(4):"
            $ ginclusion lg (cod m) gsig2
  ins' (l,m) dgr = insertLink (mr' m) globalDef l dgr
  in foldr ins' dg' $ zip links mrs


insertLink :: GMorphism -> DGLinkType -> NamedLink -> DGraph
           -> DGraph
insertLink m lType link dg = let
  -- I wish i could get this out of here.. the node is looked up for its
  -- theory in getLinkMorphism just below..
  (i,_) = fromMaybe (error "FromXml.insertLink: node not found")
        $ findNodeByName (src link) dg
  (j,_) = fromMaybe (error "FromXml.insertLink: node not found")
        $ findNodeByName (trg link) dg
  in snd $ insLEdgeDG (i,j, defDGLink m lType SeeTarget) dg


extractMorphism :: LogicGraph -> DGraph -> NamedLink -> GMorphism
extractMorphism lg dg l = let
  sgn = signOf $ dgn_theory $ snd $ fromMaybe
          (error "FromXml.extractMorphism: source node missing")
          $ findNodeByName (src l) dg
  in case findChild (unqual "GMorphism") (element l) of
    Nothing -> error $
      "FromXml.extractMorphism: Link has no Morphism!" ++ printLinks [l]
    Just mor -> let
      nm = fromMaybe (error "FromXml.extractMorphism: No name attribute")
         $ getAttrVal "name" mor
      symbs = parseSymbolMap mor
      in propagateErrors "FromXml.extractMorphism:"
         $ getGMorphism lg sgn nm symbs


parseSymbolMap :: Element -> String
parseSymbolMap = intercalate ", "
               . map ( intercalate " |-> "
               . map strContent . elChildren )
               . deepSearch ["map"]


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


insertNode :: G_theory -> NamedNode -> DGraph -> DGraph
insertNode gt x dg = let ans = globalAnnos dg
                         lbl = mkDGNodeLab gt ans x
                         n = getNewNodeDG dg
  in insLNodeDG (n,lbl) dg


-- | A Node is looked up via its name in the DGraph. Returns the node only
-- if one single node is found for the respective name, otherwise an error
-- is thrown.
findNodeByName :: String -> DGraph -> Maybe (LNode DGNodeLab)
findNodeByName s dg = case lookupNodeByName s dg of
  [n] -> Just n
  [] -> Nothing
  _ -> error $
    "FromXml.findNodeByName: ambiguous occurence for " ++ s ++ "!"


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
              Just tr -> (Link sr tr e) : r
              Nothing -> r
            Nothing -> r
  isDef l = isInfixOf "Def" $ linkTypeStr l


extractGlobalAnnos :: Element -> GlobalAnnos
extractGlobalAnnos dgEle = case findChild (unqual "Global") dgEle of
  Nothing -> emptyGlobalAnnos
  Just gl -> propagateErrors "FromXml.extractGlobalAnnos" $ getGlobalAnnos $
           unlines $ map strContent $ findChildren (unqual "Annotation") gl


-- | Generates a new DGNodeLab with a startoff-G_theory and an Element
mkDGNodeLab :: G_theory -> GlobalAnnos -> NamedNode -> DGNodeLab
mkDGNodeLab gt annos (name, el) = let
  specs = case findChild (unqual "Reference") el of
    Just rf -> unlines $ map strContent $ findChildren (unqual "Signature") rf
    Nothing -> unlines $ map strContent
             $ deepSearch ["Axiom","Theorem","Symbol"] el
  (response,message) = extendByBasicSpec annos specs gt
  in case response of
       Failure _ -> error $ ("FromXml.mkDGNodeLab (" ++ name ++ "): ") 
                     ++ message
       Success gt' _ symbs _ ->
         newNodeLab (parseNodeName name) (DGBasicSpec Nothing symbs) gt'


-- | custom xml-search for not only immediate children
deepSearch :: [String] -> Element -> [Element]
deepSearch tags' ele = rekSearch ele where
  tags = map unqual tags'
  rekSearch e = filtr e ++ concat (map filtr (elChildren e))
  filtr = filterChildrenName (`elem` tags)
