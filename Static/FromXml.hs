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

import Common.AnalyseAnnos (getGlobalAnnos)
import Common.Consistency (Conservativity (..))
import Common.GlobalAnnotations (GlobalAnnos, emptyGlobalAnnos)
import Common.LibName (LibName (..), noTime, setFilePath, emptyLibName)
import Common.Result
import Common.ResultT
import Common.Utils (readMaybe)
import Common.XUpdate (getAttrVal)

import Common.DocUtils (showDoc)

import Comorphisms.LogicGraph (logicGraph)

import Control.Monad.Trans (lift)
import Control.Monad (foldM)

import Data.List (partition, intercalate, isInfixOf)
import qualified Data.Graph.Inductive.Graph as Graph (Node)
import qualified Data.Map as Map (lookup, insert, empty)

import Driver.Options

import Logic.ExtSign (ext_empty_signature)
import Logic.Grothendieck
import Logic.Logic (AnyLogic (..), cod, composeMorphisms)
import Logic.Prover (noSens)

import Text.XML.Light

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
  unlines . map show'


-- * Top-Level functions

{- | main function; receives a FilePath and calls fromXml upon that path,
using an empty DGraph and initial LogicGraph. -}
readDGXmlR :: HetcatsOpts -> FilePath -> ResultT IO (LibName, LibEnv)
readDGXmlR opts path = do
  lift $ putIfVerbose opts 2 $ "Reading " ++ path
  xml' <- lift $ readFile path
  liftR $ case parseXMLDoc xml' of
    Nothing ->
      fail $ "failed to parse XML file: " ++ path
    Just xml -> case getAttrVal "filename" xml of
      Nothing ->
        fail $ "missing DGraph name attribute\n" ++
          unlines (take 5 $ lines xml')
      Just nm -> do
        let ln = setFilePath nm noTime $ emptyLibName nm
        an <- extractGlobalAnnos xml
        dg <- fromXml logicGraph emptyDG {globalAnnos = an} xml
        return (ln, Map.insert ln dg Map.empty)

-- | top-level function
readDGXml :: HetcatsOpts -> FilePath -> IO (Maybe (LibName, LibEnv))
readDGXml opts path = do
    Result ds res <- runResultT $ readDGXmlR opts path
    showDiags opts ds
    return res

{- | main function; receives a logicGraph, an initial DGraph and an xml
element, then adds all nodes and edges from the element into the DGraph -}
fromXml :: LogicGraph -> DGraph -> Element -> Result DGraph
fromXml lg dg el = case Map.lookup (currentLogic lg) (logics lg) of
  Nothing ->
    fail "current logic was not found in logicMap"
  Just (Logic lid) -> do
    let emptyTheory = G_theory lid (ext_empty_signature lid)
                    startSigId noSens startThId
    nodes <- extractNodeElements el
    (defLinks, thmLinks) <- extractLinkElements el
    (dg', depNodes) <- initialiseNodes emptyTheory nodes defLinks dg
    dg1 <- insertNodesAndDefLinks lg depNodes defLinks dg'
    dg2 <- insertThmLinks lg thmLinks dg1
    return $ computeDGraphTheories Map.empty dg2


-- * reconstructing the development graph

{- | All nodes that do not have dependencies via the links are processed at the
beginning and written into the DGraph. Returns the resulting DGraph and the
list of nodes that have not been stored (i.e. have dependencies). -}
initialiseNodes :: G_theory -> [NamedNode] -> [NamedLink] -> DGraph
                -> Result (DGraph, [NamedNode])
initialiseNodes gt nodes links dg = do
  let targets = map trg links
      -- all nodes that are not target of any link are considered independent
      (dep, indep) = partition ((`elem` targets) . fst) nodes
  dg' <- foldM (insertNode gt) dg indep
  return (dg', dep)


{- | main loop: in every step, all links are collected of which the source node
has been written into DGraph already. Upon these, further nodes are written
in each step until the list of remaining links reaches null. -}
insertNodesAndDefLinks :: LogicGraph -> [NamedNode] -> [NamedLink] -> DGraph
                       -> Result DGraph
insertNodesAndDefLinks _ _ [] dg = return dg
insertNodesAndDefLinks lg nodes links dg = let
  (cur, lftL) = splitLinks dg links
  in if (not . null) cur
    then do
      (dg', lftN) <- iterateNodes lg nodes cur dg
      insertNodesAndDefLinks lg lftN lftL dg'
    else fail $
      "some elements cannot be reached!\n" ++ printLinks lftL


{- | Help function for insertNodesAndDefLinks. Given a list of links, it
partitions the links depending on if they can be processed in one step. -}
splitLinks :: DGraph -> [NamedLink] -> ([NamedLink], [NamedLink])
splitLinks dg = killMultTrg . partition hasSource where
  hasSource l = case lookupNodeByName (src l) dg of
    [] -> False
    _ -> True
  killMultTrg (hasSrc, noSrc) = let noSrcTrgs = map trg noSrc in
    foldr (\ l (r, r') -> if elem (trg l) noSrcTrgs
      then (r, l : r') else (l : r, r')) ([], noSrc) hasSrc


{- | Help function for insertNodesAndDefLinks. Given the currently processable
links and the total of remaining nodes, it stores all processable elements
into the DGraph. Returns the updated DGraph and the list of remaining nodes. -}
iterateNodes :: LogicGraph -> [NamedNode] -> [NamedLink] -> DGraph
             -> Result (DGraph, [NamedNode])
iterateNodes _ nodes [] dg = return (dg, nodes)
iterateNodes _ [] links _ = fail $
  "some links are missing their target nodes!\n" ++ printLinks links
iterateNodes lg (x@(name, _) : xs) links dg =
  case partitionWith trg name links of
    ([], _) -> do
      (dg', xs') <- iterateNodes lg xs links dg
      return (dg', x : xs')
    (lCur, lLft) -> do
      dg' <- insNdAndDefLinks lg x lCur dg
      iterateNodes lg xs lLft dg'

partitionWith :: Eq a => (NamedLink -> a) -> a -> [NamedLink]
              -> ([NamedLink], [NamedLink])
partitionWith f v = partition ((== v) . f)


-- | inserts all theorem link into the previously constructed dgraph
insertThmLinks :: LogicGraph -> [NamedLink] -> DGraph -> Result DGraph
insertThmLinks lg links dg' = foldM ins' dg' links where
  ins' dg l = do
    (i, mr) <- extractMorphism lg dg l
    (j, gsig) <- signOfNode (trg l) dg
    morph <- finalizeMorphism lg mr gsig
    insertLink i j morph (lType l) dg


{- | inserts a new node into the dgraph as well as all deflinks that target
this particular node -}
insNdAndDefLinks :: LogicGraph -> NamedNode -> [NamedLink] -> DGraph
                 -> Result DGraph
insNdAndDefLinks lg trgNd links dg = do
  mrs <- mapM (extractMorphism lg dg) links
  gsig1 <- gsigManyUnion lg $ map (cod . snd) mrs
  let gt = case gsig1 of
             G_sign lid sg sId -> noSensGTheory lid sg sId
  dg' <- insertNode gt dg trgNd
  (j, gsig2) <- signOfNode (fst trgNd) dg'
  let ins' dgR ((i, mr), l) = do
        morph <- finalizeMorphism lg mr gsig2
        insertLink i j morph (lType l) dgR
  foldM ins' dg' $ zip mrs links


-- | inserts a new link into the dgraph
insertLink :: Graph.Node -> Graph.Node -> GMorphism -> DGLinkType -> DGraph
           -> Result DGraph
insertLink i j mr tp = return . snd
  . insLEdgeDG (i, j, defDGLink mr tp SeeTarget)


-- | inserts a new node into the dgraph
insertNode :: G_theory -> DGraph -> NamedNode -> Result DGraph
insertNode gt dg x = do
  let an = globalAnnos dg
      n = getNewNodeDG dg
  lbl <- mkDGNodeLab gt an x
  return $ insLNodeDG (n, lbl) dg


-- * logic calculations

{- | given a links intermediate morphism and its target nodes signature,
this function calculates the final morphism for this link -}
finalizeMorphism :: LogicGraph -> GMorphism -> G_sign -> Result GMorphism
finalizeMorphism lg mr sg = do
        mr1 <- ginclusion lg (cod mr) sg
        composeMorphisms mr mr1


-- * Utils

{- | A Node is looked up via its name in the DGraph. Returns the nodes
signature, but only if one single node is found for the respective name.
Otherwise an error is thrown. -}
signOfNode :: String -> DGraph -> Result (Graph.Node, G_sign)
signOfNode nd dg = case lookupNodeByName nd dg of
  [] -> fail $ "required node [" ++ nd ++ "] was not found in DGraph!"
  [(j, lbl)] -> do
    return (j, signOf (dgn_theory lbl))
  _ -> fail $ "ambiguous occurence for node [" ++ nd ++ "]!"


-- * Element extraction

{- | extracts the intermediate morphism for a link, using the xml data and the
signature of the (previously inserted) source node -}
extractMorphism :: LogicGraph -> DGraph -> NamedLink
                -> Result (Graph.Node, GMorphism)
extractMorphism lg dg l = do
  (i, sgn) <- signOfNode (src l) dg
  case findChild (unqual "GMorphism") (element l) of
    Nothing -> fail $
      "Links morphism description is missing!\n" ++ printLinks [l]
    Just mor -> do
      nm <- getAttrVal "name" mor
      let symbs = parseSymbolMap mor
      mor' <- getGMorphism lg sgn nm symbs
      return (i, mor')

parseSymbolMap :: Element -> String
parseSymbolMap = intercalate ", "
               . map ( intercalate " |-> "
               . map strContent . elChildren )
               . deepSearch ["map"]


{- | Generates a new DGNodeLab with a startoff-G_theory, an Element and the
the DGraphs Global Annotations -}
mkDGNodeLab :: G_theory -> GlobalAnnos -> NamedNode -> Result DGNodeLab
mkDGNodeLab gt annos (name, el) = let
  parseSpecs specElems = let
    specs = unlines $ map strContent specElems
    (response, msg) = extendByBasicSpec annos specs gt
    in case response of
      Success gt' _ symbs _ -> return (gt', symbs)
      Failure _ -> fail 
        $ "[ " ++ name ++ " ]\n" ++ showDoc (signOf gt) "\n" ++ msg
  in case findChild (unqual "Reference") el of
    -- Case #1: regular node
    Nothing -> let ch1 = deepSearch ["Axiom", "Theorem"] el 
                   ch2 = case findChild (unqual "Basicspec") el of
                     Just ch -> [ch]
                     Nothing -> findChildren (unqual "Signature") el
               in do
      (gt', symbs) <- parseSpecs $ ch1 ++ ch2
      return $ newNodeLab (parseNodeName name) (DGBasicSpec Nothing symbs) gt'
    -- Case #2: reference node
    Just rf -> do
      (gt', _) <- parseSpecs $ findChildren (unqual "Signature") rf
      {- using DGRef currently leads to runtime errors.
      see revision 14911 for such an approach -}
      return $ newNodeLab (parseNodeName name) DGBasic gt'


{- | All nodes are taken from the xml-element. Then, the name-attribute is
looked up and stored alongside the node for easy access. Nodes with no names
are ignored. -}
extractNodeElements :: Element -> Result [NamedNode]
extractNodeElements = foldM labelNode [] . findChildren (unqual "DGNode") where
  labelNode r e = do
    nm <- getAttrVal "name" e
    return $ (nm, e) : r


{- | All links are taken from the xml-element and stored alongside their source
and target information. The links are then partitioned depending on if they
are theorem or definition links. -}
extractLinkElements :: Element -> Result ([NamedLink], [NamedLink])
extractLinkElements el = do
  l1 <- foldM labelLink [] $ findChildren (unqual "DGLink") el
  return $ partition isDef l1 where
    isDef = isDefEdge . lType
    labelLink r e = do
      sr <- getAttrVal "source" e
      tr <- getAttrVal "target" e
      tp <- extractLinkType e
      return $ Link sr tr tp e : r


-- | reads the type of a link from the xml data
extractLinkType :: Element -> Result DGLinkType
extractLinkType l = do
  tp <- case findChild (unqual "Type") l of
    Nothing -> fail "Links type description is missing!"
    Just xy -> return $ strContent xy
  if tp == "HidingDefInc" then return HidingDefLink else do
    let sc = if isInfixOf "Global" tp then Global else Local
    if isInfixOf "Def" tp
      -- Case #1: DefinitionLink, global or local
      then return $ localOrGlobalDef sc None
      else if not $ isInfixOf "Thm" tp
        then fail $ "unknown link type!\n" ++ tp
          else case findChild (unqual "Status") l of
          -- Case #2: Unproven theorem link, global or local
          Nothing -> return $ localOrGlobalThm sc None
          Just st -> if strContent st /= "Proven"
            then fail $ "unknown links status!\n" ++ strContent st
            -- Case #3: Proven theorem link, global or local
            else let
              rl = case findChild (unqual "Rule") l of
                Nothing -> "no rule"
                Just r' -> strContent r'
              cc = case findChild (unqual "ConsStatus") l of
                Nothing -> None
                Just c' -> case readMaybe $ strContent c' of
                  Just consv -> consv
                  Nothing -> None
              lkind = ThmLink $ Proven (DGRule rl) emptyProofBasis
              in return $ ScopedLink sc lkind $ mkConsStatus cc


-- | extracts the global annotations from the xml-graph
extractGlobalAnnos :: Element -> Result GlobalAnnos
extractGlobalAnnos dgEle = case findChild (unqual "Global") dgEle of
  Nothing -> return emptyGlobalAnnos
  Just gl -> getGlobalAnnos $ unlines $ map strContent
    $ findChildren (unqual "Annotation") gl


-- | custom xml-search for not only immediate children
deepSearch :: [String] -> Element -> [Element]
deepSearch tags' ele = rekSearch ele where
  tags = map unqual tags'
  rekSearch e = filtr e ++ concatMap filtr (elChildren e)
  filtr = filterChildrenName (`elem` tags)
