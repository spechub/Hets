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

import Data.List (partition, intercalate)
import Data.Maybe (fromMaybe)
import qualified Data.Graph.Inductive.Graph as Graph (Node)
import qualified Data.Map as Map (lookup, insert, empty)
import qualified Data.Set as Set (Set)

import Driver.Options
import Driver.ReadFn (findFileOfLibNameAux)

import Logic.ExtSign (ext_empty_signature)
import Logic.Grothendieck
import Logic.Logic (AnyLogic (..), cod, composeMorphisms)
import Logic.Prover (noSens)

import Text.XML.Light

{- -------------
Data Types -}

{- | for faster access, some elements attributes are stored alongside
as a String -}
type NamedNode = (String, Element)

data NamedLink = Link { src :: String
                      , trg :: String
                      , lType :: DGEdgeType
                      , element :: Element }

{- ----------------------
Top-Level Functions -}

-- | top-level function
readDGXml :: HetcatsOpts -> FilePath -> IO (Maybe (LibName, LibEnv))
readDGXml opts path = do
    Result ds res <- runResultT $ readDGXmlR opts path Map.empty
    showDiags opts ds
    return res

{- | main function; receives a FilePath and calls fromXml upon that path,
using an initial LogicGraph. -}
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

{- | main function; receives a logicGraph, an initial LibEnv and an Xml
element, then adds all nodes and edges from this element into a DGraph -}
fromXml :: HetcatsOpts -> LogicGraph -> LibName -> LibEnv -> Element
        -> ResultT IO (LibName, LibEnv)
fromXml opts lg ln lv xml = do
    lo <- lookupCurrentLogic "fromXml:" lg
    an <- extractGlobalAnnos xml
    let dg = emptyDG { globalAnnos = an }
    nodes <- extractNodeElements xml
    (defLk, thmLk) <- extractLinkElements xml
    (res0, depNd) <- initialise opts (emptyTheory lo) nodes defLk (dg, lv)
    res1 <- insertNodesAndDefLinks opts lg depNd defLk res0
    res2 <- insertThmLinks lg thmLk res1
    return (ln, computeLibEnvTheories $ uncurry (Map.insert ln) res2)

{- ------------------------------------------------
Reconstruct the Development Graph, high level -}

{- | All nodes that do not have dependencies via the links are processed at the
beginning and written into the DGraph. Returns the resulting DGraph and the
list of nodes that have not been stored (i.e. have dependencies). -}
initialise :: HetcatsOpts -> G_theory -> [NamedNode] -> [NamedLink]
           -> (DGraph, LibEnv) -> ResultT IO ((DGraph, LibEnv), [NamedNode])
initialise opts gt nodes links dglv = do
  let targets = map trg links
      -- all nodes that are not target of any link are considered independent
      (dep, indep) = partition ((`elem` targets) . fst) nodes
  (dglv') <- foldM (flip $ insertNode opts gt) dglv indep
  return (dglv', dep)

-- | inserts all theorem link into the previously constructed dgraph
insertThmLinks :: LogicGraph -> [NamedLink] -> (DGraph, LibEnv)
               -> ResultT IO (DGraph, LibEnv)
insertThmLinks lg links (dg, lv) = do
  dg' <- foldM ins' dg links
  return (dg', lv) where
    ins' dgR l = do
        (i, mr, tp) <- getTypeAndMorphism lg dgR l
        (j, gsig) <- signOfNode (trg l) dgR
        morph <- finalizeMorphism lg False mr gsig
        insertLink i j morph tp dgR

{- | main loop: in every step, all links are collected of which the source node
has been written into DGraph already. Upon these, further nodes are written in
each step until the list of remaining links reaches null. -}
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

{- | Help function for insertNodesAndDefLinks. Given the currently processable
links and the total of remaining nodes, it stores all processable elements
into the DGraph. Returns the updated DGraph and the list of remaining nodes. -}
iterateNodes :: HetcatsOpts -> LogicGraph -> [NamedNode] -> [NamedLink]
             -> (DGraph, LibEnv) -> ResultT IO ((DGraph, LibEnv), [NamedNode])
iterateNodes _ _ nodes [] dglv = return (dglv, nodes)
iterateNodes _ _ [] links _ = fail $
  "some links are missing their target nodes!\n" ++ printLinks links
iterateNodes opts lg (x@(name, _) : xs) links dglv =
  case partition ((== name) . trg) links of
    ([], _) -> do
      (dglv', xs') <- iterateNodes opts lg xs links dglv
      return (dglv', x : xs')
    (lCur, lLft) -> do
      dglv' <- insertNodeAndLinks opts lg x lCur dglv
      iterateNodes opts lg xs lLft dglv'

{- | inserts a new node into the dgraph as well as all definition links that
target this particular node -}
insertNodeAndLinks :: HetcatsOpts -> LogicGraph -> NamedNode -> [NamedLink]
                 -> (DGraph, LibEnv) -> ResultT IO (DGraph, LibEnv)
insertNodeAndLinks opts lg trgNd links (dg, lv) = do
  mrs <- mapM (getTypeAndMorphism lg dg) links
  {- for HidingDefLinks, the target node signature and link morphisms are
  different. -}
  let isHiding = (== HidingDef) . edgeTypeModInc . lType
  ((dg', lv'), hid) <- case partition isHiding links of
    -- case #1: none hiding def links
    ([], _) -> do
      gsig1 <- liftR $ gsigManyUnion lg $ map (\ (_, m, _) -> cod m) mrs
      let gt = case gsig1 of
                 G_sign lid sg sId -> noSensGTheory lid sg sId
      dglv <- insertNode opts gt trgNd (dg, lv)
      return (dglv, False)
    -- case #2: only hiding def links
    (_, []) -> do
        lo <- lookupCurrentLogic (fst trgNd) lg
        dglv <- insertNode opts (emptyTheory lo) trgNd (dg, lv)
        return (dglv, True)
    -- case #3: mixture. not implemented!
    _ -> fail "mix of HidingDefLinks and other links pointing at a single node"
  (j, gsig2) <- signOfNode (fst trgNd) dg'
  let ins' dgR (i, mr, tp) = do
        morph <- finalizeMorphism lg hid mr gsig2
        insertLink i j morph tp dgR
  dg'' <- foldM ins' dg' mrs
  return (dg'', lv')

{- ------------------------------------------------------
Reconstruct the Development Graph, [link insertion] -}

{- | given a links intermediate morphism and its target nodes signature,
this function calculates the final morphism for this link -}
finalizeMorphism :: LogicGraph -> Bool -> GMorphism -> G_sign
                 -> ResultT IO GMorphism
finalizeMorphism lg hid mr sg = liftR $ if hid
  then ginclusion lg sg (cod mr)
  else do
    mr1 <- ginclusion lg (cod mr) sg
    composeMorphisms mr mr1

-- | inserts a new link into the dgraph
insertLink :: Graph.Node -> Graph.Node -> GMorphism -> DGLinkType -> DGraph
           -> ResultT IO DGraph
insertLink i j mr tp = return .
  insLEdgeNubDG (i, j, defDGLink mr tp SeeTarget)

{- | extracts the intermediate morphism for a link, using the xml data and the
signature of the (previously inserted) source node -}
getTypeAndMorphism :: LogicGraph -> DGraph -> NamedLink
                -> ResultT IO (Graph.Node, GMorphism, DGLinkType)
getTypeAndMorphism lg dg (Link srN _ tp l) =
  case findChild (unqual "GMorphism") l of
    Nothing -> fail "Links morphism description is missing!"
    Just mor -> let
        parseSymbMap = intercalate ", " . map ( intercalate " |-> "
          . map strContent . elChildren ) . deepSearch ["map"]
        symbs = parseSymbMap mor
        rl = case findChild (unqual "Rule") l of
            Nothing -> "no rule"
            Just r' -> strContent r'
        cc = case findChild (unqual "ConsStatus") l of
            Nothing -> None
            Just c' -> fromMaybe None $ readMaybe $ strContent c'
        in do
          nm <- getAttrVal "name" mor
          (i, sg1) <- signOfNode srN dg
          (sg2, lTp) <- getTypeAndMorAux lg dg (edgeTypeModInc tp)
              (getAttrVal "morphismsource" mor) sg1 cc rl
          mr' <- liftR $ getGMorphism lg sg2 nm symbs
          return (i, mr', lTp)

{- depending on the type of the link, the correct DGLinkType and the signature
for the (external) morphism are extracted here -}
getTypeAndMorAux :: LogicGraph -> DGraph -> DGEdgeTypeModInc -> Maybe String
       -> G_sign -> Conservativity -> String -> ResultT IO (G_sign, DGLinkType)
getTypeAndMorAux lg dg eTp mSrc sg@(G_sign slid _ _) cc rl = let
  emptySig = G_sign slid (ext_empty_signature slid) startSigId
  mkRtVAL sg' tp = return (sg', tp)
  in case eTp of
    HetDef -> fail "HetDef Edgetype not implemented yet!"
    HidingDef -> mkRtVAL sg HidingDefLink
    GlobalDef -> mkRtVAL sg $ localOrGlobalDef Global cc
    LocalDef -> mkRtVAL sg $ localOrGlobalDef Local cc
    FreeOrCofreeDef fc -> do
      (sg', mNd) <- case mSrc of
        Nothing -> return (emptySig, EmptyNode $ Logic slid)
        Just ms -> do
          (j, sg') <- signOfNode ms dg
          return (sg', JustNode $ NodeSig j sg')
      mkRtVAL sg' $ FreeOrCofreeDefLink fc mNd
    ThmType thTp prv _ _ -> let
      lStat = if not prv then LeftOpen
          else Proven (DGRule rl) emptyProofBasis
      in case thTp of
        HidingThm -> do
          (i', sg') <- case mSrc of
            Just ms -> signOfNode ms dg
            Nothing -> fail "no morphism source declaration for HidingThmLink"
          mr' <- liftR $ ginclusion lg sg' sg
          mkRtVAL sg' $ HidingFreeOrCofreeThm Nothing i' mr' lStat
        FreeOrCofreeThm fc -> do
            (i', sg') <- case mSrc of
              Just ms -> signOfNode ms dg
              Nothing -> return ((-1), emptySig)
            mr' <- liftR $ ginclusion lg sg' sg
            mkRtVAL sg' $ HidingFreeOrCofreeThm (Just fc) i' mr' lStat
        GlobalOrLocalThm sc _ -> mkRtVAL sg 
          $ ScopedLink sc (ThmLink lStat) $ mkConsStatus cc

{- ------------------------------------------------------
Reconstruct the Development Graph, [node insertion] -}

{- | Generates and inserts a new DGNodeLab with a startoff-G_theory, an Element
and the the DGraphs Global Annotations -}
insertNode :: HetcatsOpts -> G_theory -> NamedNode -> (DGraph, LibEnv)
           -> ResultT IO (DGraph, LibEnv)
insertNode opts gt (name, el) (dg, lv) =
  case findChild (unqual "Reference") el of
    -- Case #1: Reference Node, ref- library will be loaded
    Just rf -> insertRefNode opts rf (name, el) (dg, lv)
    -- Case #2: Regular Node
    Nothing -> let
          n = getNewNodeDG dg
          ch1 = case findChild (unqual "Declarations") el of
                       Just ch -> deepSearch ["Symbol"] ch
                       Nothing -> findChildren (unqual "Signature") el
          ch2 = deepSearch ["Axiom", "Theorem"] el
          in do
            (gt', symbs) <- parseSpecs gt name dg $ ch1 ++ ch2
            diffSig <- liftR $ homGsigDiff (signOf gt') $ signOf gt
            let lbl = newNodeLab (parseNodeName name)
                  (DGBasicSpec Nothing diffSig symbs) gt'
            return (insLNodeDG (n, lbl) dg, lv)

insertRefNode :: HetcatsOpts -> Element -> NamedNode -> (DGraph, LibEnv)
              -> ResultT IO (DGraph, LibEnv)
insertRefNode opts rf (name, el) (dg, lv) = do
          refLib <- case getAttrVal "library" rf of
            Nothing -> fail $ "no library name for reference node " ++ name
            Just ln -> return ln
          refNod <- case getAttrVal "node" rf of
            Nothing -> fail $ "no reference node name for node " ++ name
            Just nm -> return nm
          (dg', lv') <- case Map.lookup (emptyLibName refLib) lv of
            Just dg' -> return (dg', lv)
            Nothing -> loadRefLib opts refLib lv
          (i, gt) <- case lookupNodeByName refNod dg' of
              [(i, lbl)] -> case signOf $ dgn_theory lbl of
                G_sign lid sign sId -> return (i, noSensGTheory lid sign sId)
              _ -> fail $ "reference node " ++ refNod ++ " was not found"
          (gt', _) <- parseSpecs gt name dg
                    $ deepSearch ["Axiom", "Theorem"] el
          let n = getNewNodeDG dg
              nInf = newRefInfo (emptyLibName refLib) i
              lbl = newInfoNodeLab (parseNodeName name) nInf gt'
          return (addToRefNodesDG n nInf $ insLNodeDG (n, lbl) dg, lv')

loadRefLib :: HetcatsOpts -> String -> LibEnv -> ResultT IO (DGraph, LibEnv)
loadRefLib opts ln lv = do
          mPath <- lift $ findFileOfLibNameAux opts { intype = DgXml } ln
          case mPath of
            Just path -> do
              (ln', lv') <- readDGXmlR opts path lv
              return (lookupDGraph ln' lv', lv')
            _ -> fail $ "no file exists for reference library " ++ ln

parseSpecs :: G_theory -> String -> DGraph -> [Element]
           -> ResultT IO (G_theory, Set.Set G_symbol)
parseSpecs gt' name dg specElems = let
          specs = unlines $ map strContent specElems
          (response, msg) = extendByBasicSpec (globalAnnos dg) specs gt'
          in case response of
            Success gt'' _ symbs _ -> return (gt'', symbs)
            Failure _ -> fail $ "[ " ++ name ++ " ]\n" ++ msg

{- ---------------------
Element extraction -}

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
  return $ partition (\ l -> case edgeTypeModInc $ lType l of
      ThmType _ _ _ _ -> False
      _ -> True) l1 where
    labelLink r e = do
      sr <- getAttrVal "source" e
      tr <- getAttrVal "target" e
      tp <- case findChild (unqual "Type") e of
          Just tp' -> return $ revertDGEdgeTypeName $ strContent tp'
          Nothing -> fail "links type description is missing"
      return $ Link sr tr tp e : r

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

{- --------
Utils -}

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

{- | returns a String representation of a list of links showing their
source and target nodes (used for error messages). -}
printLinks :: [NamedLink] -> String
printLinks = let show' l = src l ++ " -> " ++ trg l in
  unlines . map show'

-- | creates an entirely empty theory
emptyTheory :: AnyLogic -> G_theory
emptyTheory (Logic lid) =
  G_theory lid (ext_empty_signature lid) startSigId noSens startThId

{- | A Node is looked up via its name in the DGraph. Returns the nodes
signature, but only if one single node is found for the respective name.
Otherwise an error is thrown. -}
signOfNode :: String -> DGraph -> ResultT IO (Graph.Node, G_sign)
signOfNode nd dg = case lookupNodeByName nd dg of
  [] -> fail $ "required node [" ++ nd ++ "] was not found in DGraph!"
  [(j, lbl)] ->
    return (j, signOf (dgn_theory lbl))
  _ -> fail $ "ambiguous occurence for node [" ++ nd ++ "]!"
