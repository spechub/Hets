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

import Common.LibName (LibName (..), noTime, setFilePath, emptyLibName)
import Common.Result (propagateErrors)
import Common.XUpdate (getAttrVal)
import Common.GlobalAnnotations (GlobalAnnos, emptyGlobalAnnos)
import Common.AnalyseAnnos (getGlobalAnnos)

import Common.Consistency (Conservativity (..))

import Comorphisms.LogicGraph (logicGraph)

import Logic.ExtSign (ext_empty_signature)
import Logic.Logic (AnyLogic (..), cod, composeMorphisms)
import Logic.Prover (noSens)
import Logic.Grothendieck

import qualified Data.Map as Map (lookup, insert, empty)
import Data.List (partition, intercalate, isInfixOf)
import Data.Graph.Inductive.Graph (LNode)
import qualified Data.Graph.Inductive.Graph as Graph (Node)
import Data.Maybe (fromMaybe)

import Text.XML.Light

-- TODO sort functions into chapters


-- * Data Types


{- | for faster access, some elements attributes are stored alongside
as a String -}
type NamedNode = (String, Element)

data NamedLink = Link { src :: String
                      , trg :: String
                      , lType :: DGLinkType
                      , element :: Element }

{- | returns a String representation of a list of links showing their
source and target nodes (used for error messages). -}
printLinks :: [NamedLink] -> String
printLinks = let show' l = src l ++ " -> " ++ trg l in
  unlines . (map show')


{- | main function; receives a FilePath and calls fromXml upon that path,
using an empty DGraph and initial LogicGraph. -}
readDGXml :: FilePath -> IO (Maybe (LibName, LibEnv))
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
        ln = setFilePath nm noTime $ emptyLibName nm
        le = Map.insert ln dg Map.empty
        in return $ Just (ln, le)


{- | main function; receives a logicGraph, an initial DGraph and an xml
element, then adds all nodes and edges from the element into the DGraph -}
fromXml :: LogicGraph -> DGraph -> Element -> DGraph
fromXml lg dg el = case Map.lookup (currentLogic lg) (logics lg) of
  Nothing ->
    error "FromXml.fromXml: current logic was not found in logicMap"
  Just (Logic lid) -> let
    emptyTheory = G_theory lid (ext_empty_signature lid)
                    startSigId noSens startThId
    nodes = extractNodeElements el
    (defLinks, thmLinks) = extractLinkElements el
    (dg', depNodes) = initialiseNodes emptyTheory nodes defLinks dg
    in computeDGraphTheories Map.empty
      . insertThmLinks lg thmLinks
      . insertNodesAndDefLinks lg depNodes defLinks
      $ dg'


{- | main loop: in every step, all links are collected of which the source node
has been written into DGraph already. Upon these, further nodes are written
in each step until the list of remaining links reaches null. -}
insertNodesAndDefLinks :: LogicGraph -> [NamedNode] -> [NamedLink] -> DGraph
                       -> DGraph
insertNodesAndDefLinks _ _ [] dg = dg
insertNodesAndDefLinks lg nodes links dg = let
  (cur, lftL) = splitLinks dg links
  (dg', lftN) = iterateNodes lg nodes cur dg
  in if (not . null) cur then insertNodesAndDefLinks lg lftN lftL dg'
     else error $
      "FromXml.insertNodesAndDefLinks: remaining links cannot be processed!\n"
        ++ printLinks lftL


{- | Help function for insertNodesAndDefLinks. Given a list of links, it
partitions the links depending on if they can be processed in one step. -}
splitLinks :: DGraph -> [NamedLink] -> ([NamedLink], [NamedLink])
splitLinks dg = killMultTrg . foldr partiSrc ([], []) where
  partiSrc l (r, r') = case findNodeByName (src l) dg of
    Nothing -> (r, l : r')
    _ -> (l : r, r')
  killMultTrg (hasSrc, noSrc) = let noSrcTrgs = map trg noSrc in
    foldr (\ l (r, r') -> if elem (trg l) noSrcTrgs
      then (r, l : r') else (l : r, r')) ([], noSrc) hasSrc


{- | Help function for insertNodesAndDefLinks. Given the currently processable
links and the total of remaining nodes, it stores all processable elements
into the DGraph. Returns the updated DGraph and a list of remaining nodes. -}
iterateNodes :: LogicGraph -> [NamedNode] -> [NamedLink] -> DGraph
             -> (DGraph, [NamedNode])
iterateNodes _ nodes [] dg = (dg, nodes)
iterateNodes _ [] links _ = error $
  "FromXml.iterateNodes: remaining links targets cannot be found!\n"
    ++ printLinks links
iterateNodes lg (x@(name, _) : xs) links dg =
  case partitionWith trg name links of
    ([], _) -> let (dg', xs') = iterateNodes lg xs links dg
              in (dg', x : xs')
    (lCur, lLft) -> iterateNodes lg xs lLft
                  $ insNdAndDefLinks lg x lCur dg

partitionWith :: Eq a => (NamedLink -> a) -> a -> [NamedLink]
              -> ([NamedLink], [NamedLink])
partitionWith f v = partition ((== v) . f)


-- | inserts all theorem link into the previously constructed dgraph
insertThmLinks :: LogicGraph -> [NamedLink] -> DGraph -> DGraph
insertThmLinks lg links dg' = foldr ins' dg' links where
  ins' l dg = let
    (i, mr) = extractMorphism lg dg l
    (j, gsig) = signOfNode (trg l) dg
    morph = finalizeMorphism lg mr gsig
    in insertLink i j morph (lType l) dg


{- | inserts a new node into the dgraph as well as all deflinks that target
this particular node -}
insNdAndDefLinks :: LogicGraph -> NamedNode -> [NamedLink] -> DGraph -> DGraph
insNdAndDefLinks _ _ [] _ = error "FromXml.insNdAndDefLinks"
insNdAndDefLinks lg trgNd links dg = let
  mrs = map (extractMorphism lg dg) links
  gsig1 = propagateErrors "FromXml.insNdAndDefLinks(2):" $
    gsigManyUnion lg $ map (cod . snd) mrs
  gt = case gsig1 of
    G_sign lid sg sId -> noSensGTheory lid sg sId
  dg' = insertNode gt trgNd dg
  (j, gsig2) = signOfNode (fst trgNd) dg'
  morph mr = finalizeMorphism lg mr gsig2
  ins' ((i, mr), l) dgr = insertLink i j (morph mr) (lType l) dgr
  in foldr ins' dg' $ zip mrs links


-- | inserts a new link into the dgraph
insertLink :: Graph.Node -> Graph.Node -> GMorphism -> DGLinkType -> DGraph
           -> DGraph
insertLink i j mr tp = snd
  . insLEdgeDG (i, j, defDGLink mr tp SeeTarget)


-- | inserts a new node into the dgraph
insertNode :: G_theory -> NamedNode -> DGraph -> DGraph
insertNode gt x dg = let an = globalAnnos dg
                         lbl = mkDGNodeLab gt an x
                         n = getNewNodeDG dg
  in insLNodeDG (n, lbl) dg


-- | returns the g_sign of a node from the dgraph
signOfNode :: String -> DGraph -> (Graph.Node, G_sign)
signOfNode nd = (\ (j, lbl) -> (j, signOf (dgn_theory lbl)))
  . fromMaybe (error "FromXml.signOfNode") . findNodeByName nd


{- | given a links intermediate morphism and its target nodes signature,
this function calculates the final morphism for this link -}
finalizeMorphism :: LogicGraph -> GMorphism -> G_sign -> GMorphism
finalizeMorphism lg mr = propagateErrors "FromXml.finalizeMorphism(1):"
                       . composeMorphisms mr
                       . propagateErrors "FromXml.finalizeMorphism(2):"
                       . ginclusion lg (cod mr)


{- | extracts the intermediate morphism for a link, using the xml data and the
(previously inserted) source nodes signature -}
extractMorphism :: LogicGraph -> DGraph -> NamedLink -> (Graph.Node, GMorphism)
extractMorphism lg dg l = let
  (i, sgn) = signOfNode (src l) dg
  in case findChild (unqual "GMorphism") (element l) of
    Nothing -> error $
      "FromXml.extractMorphism: no morphism!" ++ printLinks [l]
    Just mor -> let
      nm = fromMaybe (error "FromXml.extractMorphism(2)")
         $ getAttrVal "name" mor
      symbs = parseSymbolMap mor
      in (i, propagateErrors "FromXml.extractMorphism(3):"
        $ getGMorphism lg sgn nm symbs)


parseSymbolMap :: Element -> String
parseSymbolMap = intercalate ", "
               . map ( intercalate " |-> "
               . map strContent . elChildren )
               . deepSearch ["map"]


{- | All nodes that do not have dependencies via the links are processed at the
beginning and written into the DGraph. Returns the resulting DGraph and the
list of nodes that have not been stored (i.e. have dependencies). -}
initialiseNodes :: G_theory -> [NamedNode] -> [NamedLink] -> DGraph
                -> (DGraph, [NamedNode])
initialiseNodes gt nodes links dg = let
  targets = map trg links
  -- all nodes that are not targeted by any links are considered independent
  (dep, indep) = partition ((`elem` targets) . fst) nodes
  dg' = foldr (insertNode gt) dg indep
  in (dg', dep)


{- | A Node is looked up via its name in the DGraph. Returns the node only
if one single node is found for the respective name, otherwise an error
is thrown. -}
findNodeByName :: String -> DGraph -> Maybe (LNode DGNodeLab)
findNodeByName s dg = case lookupNodeByName s dg of
  [n] -> Just n
  [] -> Nothing
  _ -> error $
    "FromXml.findNodeByName: ambiguous occurence for " ++ s ++ "!"


{- | All nodes are taken from the xml-element. Then, the name-attribute is
looked up and stored alongside the node for easy access. Nodes with no names
are ignored. -}
extractNodeElements :: Element -> [NamedNode]
extractNodeElements = foldr f [] . findChildren (unqual "DGNode") where
  f e r = case getAttrVal "name" e of
            Just name -> (name, e) : r
            Nothing -> r


{- | All links are taken from the xml-element and stored alongside their source
and target information. The links are then partitioned depending on if they
are theorem or definition links. -}
extractLinkElements :: Element -> ([NamedLink], [NamedLink])
extractLinkElements = partition isDef . foldr mkNamedLink [] .
                    findChildren (unqual "DGLink") where
  isDef = isDefEdge . lType
  mkNamedLink e r = case getAttrVal "source" e of
    Nothing -> r
    Just sr -> case getAttrVal "target" e of
      Nothing -> r
      Just tr -> Link sr tr (getLinkType e) e : r


getLinkType :: Element -> DGLinkType
getLinkType l = let
  tp = case findChild (unqual "Type") l of
    Nothing -> error "FromXml.getLinkType(1)"
    Just xy -> strContent xy
  sc = if isInfixOf "Global" tp then Global else Local
  in if isInfixOf "Def" tp
    -- Case #1: DefinitionLink, global or local
    then localOrGlobalDef sc None
    else case findChild (unqual "Status") l of
      -- Case #2: Unproven theorem link, global or local
      Nothing -> localOrGlobalThm sc None
      Just st -> if strContent st /= "Proven"
        then error "FromXml.getLinkType: unknown links status!"
        -- Case #3: Proven theorem link, global or local
        else case findChild (unqual "Rule") l of
          Nothing -> error "FromXml.getLinkType(2)"
          Just rl -> case findChild (unqual "ConsStatus") l of
            Nothing -> error "FromXml.getLinkType(3)"
            Just cc -> let
              lkind = ThmLink $ Proven (DGRule (strContent rl)) emptyProofBasis
              consv = case strContent cc of
                "Inconsistent" -> Inconsistent
                "PCons" -> PCons
                "Cons" -> Cons
                "Mono" -> Mono
                "Def" -> Def
                _ -> None
              in ScopedLink sc lkind $ mkConsStatus consv


extractGlobalAnnos :: Element -> GlobalAnnos
extractGlobalAnnos dgEle = case findChild (unqual "Global") dgEle of
  Nothing -> emptyGlobalAnnos
  Just gl -> propagateErrors "FromXml.extractGlobalAnnos" $ getGlobalAnnos $
           unlines $ map strContent $ findChildren (unqual "Annotation") gl


{- | Generates a new DGNodeLab with a startoff-G_theory, an Element and the
the DGraphs Global Annotations -}
mkDGNodeLab :: G_theory -> GlobalAnnos -> NamedNode -> DGNodeLab
mkDGNodeLab gt annos (name, el) = let
  parseSpecs specElems = let
    specs = unlines $ map strContent specElems
    (response, message) = extendByBasicSpec annos specs gt
    in case response of
      Success gt' _ symbs _ -> (gt', symbs)
      Failure _ -> error $ ("FromXml.mkDGNodeLab (" ++ name ++ "):\n")
        ++ message
  in case findChild (unqual "Reference") el of
    -- Case #1: regular node
    Nothing -> let
      (gt', symbs) = parseSpecs $ deepSearch ["Axiom", "Theorem", "Symbol"] el
      in newNodeLab (parseNodeName name) (DGBasicSpec Nothing symbs) gt'
    -- Case #2: reference node
    Just rf -> let
      (gt', _) = parseSpecs $ findChildren (unqual "Signature") rf
      refLib = case getAttrVal "library" rf of
        Nothing -> error "FromXml.mkDGNodeLab(1)"
        Just ln -> emptyLibName ln
      in newInfoNodeLab (parseNodeName name) (newRefInfo refLib (-1)) gt'

-- | custom xml-search for not only immediate children
deepSearch :: [String] -> Element -> [Element]
deepSearch tags' ele = rekSearch ele where
  tags = map unqual tags'
  rekSearch e = filtr e ++ concat (map filtr (elChildren e))
  filtr = filterChildrenName (`elem` tags)
