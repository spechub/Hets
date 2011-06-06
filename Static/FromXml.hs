{- |
Module      :  $Header$
Description :  xml input for Hets development graphs
Copyright   :  (c) Simon Ulbricht, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  tekknix@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (DevGraph)

create new or extend a Development Graph in accordance with an XML input
-}

module Static.FromXml where

import Static.ComputeTheory (computeLibEnvTheories)
import Static.DevGraph
import Static.GTheory

import Common.AnalyseAnnos (getGlobalAnnos)
import Common.Consistency (Conservativity (..))
import Common.GlobalAnnotations (GlobalAnnos, emptyGlobalAnnos)
import Common.LibName
import Common.Result (Result (..))
import Common.ResultT
import Common.Utils (readMaybe)
import Common.XUpdate (getAttrVal)

import Comorphisms.LogicGraph (logicGraph)

import Control.Monad.Trans (lift)
import Control.Monad (foldM)

import Data.List (partition, intercalate, isInfixOf)
import Data.Maybe (fromMaybe)
import qualified Data.Graph.Inductive.Graph as Graph (Node)
import qualified Data.Map as Map (lookup, insert, empty)

import Driver.Options
import Driver.ReadFn (findFileOfLibNameAux)

import Logic.ExtSign (ext_empty_signature)
import Logic.Grothendieck
import Logic.Logic (AnyLogic (..), cod, composeMorphisms)
import Logic.Prover (noSens)

import Text.XML.Light

-- import Debug.Trace

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

-- | top-level function
readDGXml :: HetcatsOpts -> FilePath -> IO (Maybe (LibName, LibEnv))
readDGXml opts path = do
    Result ds res <- runResultT $ readDGXmlR opts path Map.empty
    showDiags opts ds
    return res

{- | main function; receives a FilePath and calls fromXml upon that path,
using an empty DGraph and initial LogicGraph. -}
readDGXmlR :: HetcatsOpts -> FilePath -> LibEnv -> ResultT IO (LibName, LibEnv)
readDGXmlR opts path lv = do
  lift $ putIfVerbose opts 2 $ "Reading " ++ path
  xml' <- lift $ readFile path
  case parseXMLDoc xml' of
    Nothing ->
      fail $ "failed to parse XML file: " ++ path
    Just xml -> case getAttrVal "libname" xml of
      Nothing ->
        fail $ "missing DGraph name attribute\n" ++
          unlines (take 5 $ lines xml')
      Just nm -> do
        let ln = setFilePath nm noTime $ emptyLibName nm
        fromXml opts logicGraph ln lv xml

-- | creates an entirely empty theory
emptyTheory :: AnyLogic -> G_theory
emptyTheory (Logic lid) =
  G_theory lid (ext_empty_signature lid) startSigId noSens startThId

{- | main function; receives a logicGraph, an initial DGraph and an xml
element, then adds all nodes and edges from the element into the DGraph -}
fromXml :: HetcatsOpts -> LogicGraph -> LibName -> LibEnv -> Element
        -> ResultT IO (LibName, LibEnv)
fromXml opts lg ln lv xml = case Map.lookup (currentLogic lg) (logics lg) of
  Nothing ->
    fail "current logic was not found in logicMap"
  Just lo -> do
    nodes <- extractNodeElements xml
    (defLinks, thmLinks) <- extractLinkElements xml
    an <- extractGlobalAnnos xml
    let dg = emptyDG { globalAnnos = an }

    (dglv, depNodes) <- initialiseNodes opts (emptyTheory lo)
      nodes defLinks (dg, lv)
    (dg', lv') <- insertNodesAndDefLinks opts lg depNodes defLinks dglv
    dg'' <- insertThmLinks lg thmLinks dg'
    return (ln, computeLibEnvTheories $ Map.insert ln dg'' lv')


-- * reconstructing the development graph

{- | All nodes that do not have dependencies via the links are processed at the
beginning and written into the DGraph. Returns the resulting DGraph and the
list of nodes that have not been stored (i.e. have dependencies). -}
initialiseNodes :: HetcatsOpts -> G_theory -> [NamedNode] -> [NamedLink]
  -> (DGraph, LibEnv) -> ResultT IO ((DGraph, LibEnv), [NamedNode])
initialiseNodes opts gt nodes links dglv = do
  let targets = map trg links
      -- all nodes that are not target of any link are considered independent
      (dep, indep) = partition ((`elem` targets) . fst) nodes
  (dglv') <- foldM (flip $ insertNode opts gt) dglv indep
  return (dglv', dep)


{- | main loop: in every step, all links are collected of which the source node
has been written into DGraph already. Upon these, further nodes are written
in each step until the list of remaining links reaches null. -}
insertNodesAndDefLinks :: HetcatsOpts -> LogicGraph -> [NamedNode]
  -> [NamedLink] -> (DGraph, LibEnv) -> ResultT IO (DGraph, LibEnv)
insertNodesAndDefLinks _ _ _ [] dglv = return dglv
insertNodesAndDefLinks opts lg nodes links (dg, lv) = let
  (cur, lftL) = splitLinks dg links
  in if (not . null) cur
    then do
      (dglv', lftN) <- iterateNodes opts lg nodes cur (dg, lv)
      insertNodesAndDefLinks opts lg lftN lftL dglv'
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
iterateNodes :: HetcatsOpts -> LogicGraph -> [NamedNode] -> [NamedLink]
             -> (DGraph, LibEnv) -> ResultT IO ((DGraph, LibEnv), [NamedNode])
iterateNodes _ _ nodes [] dglv = return (dglv, nodes)
iterateNodes _ _ [] links _ = fail $
  "some links are missing their target nodes!\n" ++ printLinks links
iterateNodes opts lg (x@(name, _) : xs) links dglv =
  case partitionWith trg name links of
    ([], _) -> do
      (dglv', xs') <- iterateNodes opts lg xs links dglv
      return (dglv', x : xs')
    (lCur, lLft) -> do
      dglv' <- insNdAndDefLinks opts lg x lCur dglv
      iterateNodes opts lg xs lLft dglv'

partitionWith :: Eq a => (NamedLink -> a) -> a -> [NamedLink]
              -> ([NamedLink], [NamedLink])
partitionWith f v = partition ((== v) . f)


-- | inserts all theorem link into the previously constructed dgraph
insertThmLinks :: LogicGraph -> [NamedLink] -> DGraph -> ResultT IO DGraph
insertThmLinks lg links dg' = foldM ins' dg' links where
  ins' dg l = do
    (i, mr) <- extractMorphism lg dg l
    (j, gsig) <- signOfNode (trg l) dg
    morph <- finalizeMorphism lg mr gsig
    insertLink i j morph (lType l) dg


{- | inserts a new node into the dgraph as well as all deflinks that target
this particular node -}
insNdAndDefLinks :: HetcatsOpts -> LogicGraph -> NamedNode -> [NamedLink]
                 -> (DGraph, LibEnv) -> ResultT IO (DGraph, LibEnv)
insNdAndDefLinks opts lg trgNd links (dg, lv) = do
  mrs <- mapM (extractMorphism lg dg) links
  ((dg', lv'), isHiding) <- case partition (isHidingDef . lType) links of
    -- case #1: none hiding def links
    ([], _) -> do
      gsig1 <- liftR $ gsigManyUnion lg $ map (cod . snd) mrs
      let gt = case gsig1 of
                 G_sign lid sg sId -> noSensGTheory lid sg sId
      dglv <- insertNode opts gt trgNd (dg, lv)
      return (dglv, False)
    -- case #2: only hiding def links
    (_, []) -> case Map.lookup (currentLogic lg) (logics lg) of
      Nothing ->
        fail "current logic was not found in logicMap"
      Just lo -> do
        dglv <- insertNode opts (emptyTheory lo) trgNd (dg, lv)
        return (dglv, True)
    -- case #3: mixture. not implemented!
    _ -> fail "mix of HidingDefLinks and other links pointing at a single node"
  (j, gsig2) <- signOfNode (fst trgNd) dg'
  let ins' dgR ((i, mr), l) = do
        morph <- if isHiding then liftR $ ginclusion lg gsig2 (cod mr)
          else finalizeMorphism lg mr gsig2
        insertLink i j morph (lType l) dgR
  dg'' <- foldM ins' dg' $ zip mrs links
  return (dg'', lv')


-- TODO: when inserting RefNodes, call addToRefNodesDG (DevGraph)!!


{- | Generates and inserts a new DGNodeLab with a startoff-G_theory, an Element
and the the DGraphs Global Annotations -}
insertNode :: HetcatsOpts -> G_theory -> NamedNode -> (DGraph, LibEnv)
           -> ResultT IO (DGraph, LibEnv)
insertNode opts gt (name, el) (dg, lv) = let
  n = getNewNodeDG dg
  parseSpecs gt' specElems = let
    specs = unlines $ map strContent specElems
    (response, msg) = extendByBasicSpec (globalAnnos dg) specs gt'
    in case response of
      Success gt'' _ symbs _ -> return (gt'', symbs)
      Failure _ -> fail
        $ "[ " ++ name ++ " ]\n" ++ msg
  in case findChild (unqual "Reference") el of
    -- Case #1: regular node
    Nothing -> let ch1 = case findChild (unqual "Declarations") el of
                     Just ch -> deepSearch ["Symbol"] ch
                     Nothing -> findChildren (unqual "Signature") el
                   ch2 = deepSearch ["Axiom", "Theorem"] el
               in do
      (gt', symbs) <- parseSpecs gt $ ch1 ++ ch2
      diffSig <- liftR $ homGsigDiff (signOf gt') $ signOf gt
      let lbl = newNodeLab (parseNodeName name)
            (DGBasicSpec Nothing diffSig symbs) gt'
      return (insLNodeDG (n, lbl) dg, lv)
    -- Case #2: reference node
    Just rf -> do
      -- (gt', _) <- parseSpecs $ findChildren (unqual "Signature") rf
      refLib <- case getAttrVal "library" rf of
        Nothing -> fail $ "no library name for reference node " ++ name
        Just ln -> return ln
      refNod <- case getAttrVal "node" rf of
        Nothing -> fail $ "no reference node name for node " ++ name
        Just nm -> return nm
      (dg', lv') <- case Map.lookup (emptyLibName refLib) lv of
        Just dg' -> return (dg', lv)
        Nothing -> loadRefLib opts refLib lv
      (i, gt') <- case lookupNodeByName refNod dg' of
          [(i, lbl)] -> case signOf $ dgn_theory lbl of
            G_sign lid sign sId -> return (i, noSensGTheory lid sign sId)
          _ -> fail $ "reference node " ++ refNod ++ " was not found"
      (gt'', _) <- parseSpecs gt' $ deepSearch ["Axiom", "Theorem"] el
      let lbl = newInfoNodeLab (parseNodeName name)
            (newRefInfo (emptyLibName refLib) i) gt''
      return (insLNodeDG (n, lbl) dg, lv')

loadRefLib :: HetcatsOpts -> String -> LibEnv
  -> ResultT IO (DGraph, LibEnv)
loadRefLib opts ln lv = do
  mPath <- lift $ findFileOfLibNameAux opts { intype = DgXml } ln
  case mPath of
    Just path -> do
      (ln', lv') <- readDGXmlR opts path lv
      return (lookupDGraph ln' lv', lv')
    _ -> fail $ "no file exists for reference library " ++ ln


-- | inserts a new link into the dgraph
insertLink :: Graph.Node -> Graph.Node -> GMorphism -> DGLinkType -> DGraph
           -> ResultT IO DGraph
insertLink i j mr tp = return
  . insLEdgeNubDG (i, j, defDGLink mr tp SeeTarget)

-- * logic calculations

{- | given a links intermediate morphism and its target nodes signature,
this function calculates the final morphism for this link -}
finalizeMorphism :: LogicGraph -> GMorphism -> G_sign -> ResultT IO GMorphism
finalizeMorphism lg mr sg = liftR $ do
        mr1 <- ginclusion lg (cod mr) sg
        composeMorphisms mr mr1


-- * Utils

{- | A Node is looked up via its name in the DGraph. Returns the nodes
signature, but only if one single node is found for the respective name.
Otherwise an error is thrown. -}
signOfNode :: String -> DGraph -> ResultT IO (Graph.Node, G_sign)
signOfNode nd dg = case lookupNodeByName nd dg of
  [] -> fail $ "required node [" ++ nd ++ "] was not found in DGraph!"
  [(j, lbl)] ->
    return (j, signOf (dgn_theory lbl))
  _ -> fail $ "ambiguous occurence for node [" ++ nd ++ "]!"


-- * Element extraction

{- | extracts the intermediate morphism for a link, using the xml data and the
signature of the (previously inserted) source node -}
extractMorphism :: LogicGraph -> DGraph -> NamedLink
                -> ResultT IO (Graph.Node, GMorphism)
extractMorphism lg dg l = do
  (i, sgn) <- signOfNode (src l) dg
  case findChild (unqual "GMorphism") (element l) of
    Nothing -> fail $
      "Links morphism description is missing!\n" ++ printLinks [l]
    Just mor -> liftR $ do
      nm <- getAttrVal "name" mor
      let symbs = parseSymbolMap mor
      mor' <- getGMorphism lg sgn nm symbs
      return (i, mor')

parseSymbolMap :: Element -> String
parseSymbolMap = intercalate ", "
               . map ( intercalate " |-> "
               . map strContent . elChildren )
               . deepSearch ["map"]


{- | All nodes are taken from the xml-element. Then, the name-attribute is
looked up and stored alongside the node for easy access. Nodes with no names
are ignored. -}
extractNodeElements :: Element -> ResultT IO [NamedNode]
extractNodeElements = foldM labelNode [] . findChildren (unqual "DGNode") where
  labelNode r e = do
    nm <- getAttrVal "name" e
    return $ (nm, e) : r


{- | All links are taken from the xml-element and stored alongside their source
and target information. The links are then partitioned depending on if they
are theorem or definition links. -}
extractLinkElements :: Element -> ResultT IO ([NamedLink], [NamedLink])
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
extractLinkType :: Element -> ResultT IO DGLinkType
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
                Just c' -> fromMaybe None $ readMaybe $ strContent c'
              lkind = ThmLink $ Proven (DGRule rl) emptyProofBasis
              in return $ ScopedLink sc lkind $ mkConsStatus cc


-- | extracts the global annotations from the xml-graph
extractGlobalAnnos :: Element -> ResultT IO GlobalAnnos
extractGlobalAnnos dgEle = case findChild (unqual "Global") dgEle of
  Nothing -> return emptyGlobalAnnos
  Just gl -> liftR $ getGlobalAnnos $ unlines $ map strContent
    $ findChildren (unqual "Annotation") gl


-- | custom xml-search for not only immediate children
deepSearch :: [String] -> Element -> [Element]
deepSearch tags' ele = rekSearch ele where
  tags = map unqual tags'
  rekSearch e = filtr e ++ concatMap filtr (elChildren e)
  filtr = filterChildrenName (`elem` tags)
