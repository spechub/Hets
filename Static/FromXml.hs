{- |
Module      :  ./Static/FromXml.hs
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
import Static.DgUtils
import Static.GTheory
import Static.FromXmlUtils
import Static.XGraph

import Common.LibName
import Common.Result (Result (..))
import Common.ResultT
import Common.XmlParser

import Comorphisms.LogicGraph (logicGraph)

import Control.Monad.Trans (lift)
import Control.Monad (foldM, unless)
import qualified Control.Monad.Fail as Fail

import qualified Data.Graph.Inductive.Graph as Graph (Node)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Driver.Options
import Driver.ReadFn (findFileOfLibNameAux)

import Logic.ExtSign (ext_empty_signature)
import Logic.Grothendieck
import Logic.Logic (AnyLogic (..), cod, composeMorphisms)
import Logic.Prover (noSens)

import Text.XML.Light (Element)

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
  xml' <- lift $ readXmlFile path
  res <- lift $ parseXml xml'
  case res of
    Right xml -> rebuiltDgXml opts lv xml
    Left err -> Fail.fail $ "failed to parse XML file: " ++ path ++ "\n" ++ err

-- | call rebuiltDG with only a LibEnv and an Xml-Element
rebuiltDgXml :: HetcatsOpts -> LibEnv -> Element -> ResultT IO (LibName, LibEnv)
rebuiltDgXml opts lv xml = do
      xg <- liftR $ xGraph xml
      res <- rebuiltDG opts logicGraph xg lv
      let ln = libName xg
      return (ln, computeLibEnvTheories $ uncurry (Map.insert ln) res)

{- | reconstructs the Development Graph via a previously created XGraph-
structure. -}
rebuiltDG :: HetcatsOpts -> LogicGraph -> XGraph -> LibEnv
          -> ResultT IO (DGraph, LibEnv)
rebuiltDG opts lg (XGraph _ ga i thmLk nds body) lv = do
  (dg, lv') <- rebuiltBody body lv
  dg' <- insertThmLinks lg dg $ mkEdgeMap thmLk
  return (dg', lv') where
    rebuiltBody bd lv' = case bd of
        [] ->
          foldM (flip $ insertFirstNode opts lg)
            (emptyDG { globalAnnos = ga, getNewEdgeId = i }, lv') nds
        bs : bd' -> do
          res0 <- rebuiltBody bd' lv'
          foldM (\ dl (lKs, nd) ->
            insertStep opts lg nd lKs dl)
            res0 bs

-- | inserts a new node as well as all definition links pointing at that node
insertStep :: HetcatsOpts -> LogicGraph -> XNode -> [XLink] -> (DGraph, LibEnv)
           -> ResultT IO (DGraph, LibEnv)
insertStep opts lg xNd lks (dg, lv) = do
  mrs <- mapM (getTypeAndMorphism lg dg) lks
  G_sign lid sg sId <- getSigForXNode lg dg mrs
  let j = getNewNodeDG dg
  (gt2, dg', lv') <-
    insertNode opts lg (Just $ noSensGTheory lid sg sId) xNd j (dg, lv)
  dg'' <- foldM (insertLink lg j (signOf gt2)) dg' mrs
  return (dg'', lv')

insertLink :: LogicGraph -> Graph.Node -> G_sign -> DGraph
            -> (Graph.Node, GMorphism, DGLinkType, XLink) -> ResultT IO DGraph
insertLink lg j gs dg (i, mr, tp, lk) = do
            lkLab <- finalizeLink lg lk mr gs tp
            return $ insEdgeAsIs (i, j, lkLab) dg

-- | inserts theorem links
insertThmLinks :: LogicGraph -> DGraph -> EdgeMap -> ResultT IO DGraph
insertThmLinks lg p = foldM (\ dg (tgt, sm) -> do
  (j, gsig) <- signOfNode tgt dg
  insertTarThmLinks lg j gsig dg sm) p . Map.toList

insertTarThmLinks :: LogicGraph -> Graph.Node -> G_sign
  -> DGraph -> Map.Map String [XLink] -> ResultT IO DGraph
insertTarThmLinks lg j tgt p = foldM (\ dg (src, ls) -> do
  (i, gsig) <- signOfNode src dg
  foldM (\ dg' xLk -> do
      (mr, tp) <- getTypeAndMorphism1 lg dg gsig xLk
      insertLink lg j tgt dg' (i, mr, tp, xLk)) dg ls) p . Map.toList

{- | given a links intermediate morphism and its target nodes signature,
this function calculates the final morphism for this link -}
finalizeLink :: LogicGraph -> XLink -> GMorphism -> G_sign -> DGLinkType
             -> ResultT IO DGLinkLab
finalizeLink lg xLk mr sg tp = do
  mr' <- liftR $ case edgeTypeModInc $ lType xLk of
    HidingDef -> ginclusion lg sg (cod mr)
    _ -> do
      mr1 <- ginclusion lg (cod mr) sg
      composeMorphisms mr mr1
  return $ defDGLinkId mr' tp SeeTarget $ edgeId xLk

{- | based upon the morphisms of ingoing deflinks, calculate the initial
signature to be used for node insertion -}
getSigForXNode :: LogicGraph -> DGraph
               -> [(Graph.Node, GMorphism, DGLinkType, XLink)]
               -> ResultT IO G_sign
getSigForXNode lg dg mrs = case mrs of
    [] -> Fail.fail "insertStep: empty link list"
    (_, _, FreeOrCofreeDefLink _ _, xLk) : rt -> do
        unless (null rt)
          $ Fail.fail "unexpected non-singleton free or cofree def link"
        fmap snd $ signOfNode (source xLk) dg
    _ -> liftR $ gsigManyUnion lg $ map (\ (_, m, _, _) -> cod m) mrs

-- | gathers information for an XLink using its source nodes signature
getTypeAndMorphism :: LogicGraph -> DGraph -> XLink
                   -> ResultT IO (Graph.Node, GMorphism, DGLinkType, XLink)
getTypeAndMorphism lg dg xLk = do
  (i, sg1) <- signOfNode (source xLk) dg
  (mr', lTp) <- getTypeAndMorphism1 lg dg sg1 xLk
  return (i, mr', lTp, xLk)

getTypeAndMorphism1 :: LogicGraph -> DGraph -> G_sign -> XLink
  -> ResultT IO (GMorphism, DGLinkType)
getTypeAndMorphism1 lg dg sg1 xLk = do
    (sg2, lTp) <- getTypeAndMorAux lg dg sg1 xLk
    mr' <- liftR $ getGMorphism lg sg2 (mr_name xLk) (mapping xLk)
    return (mr', lTp)

{- depending on the type of the link, the correct DGLinkType and the signature
for the (external) morphism are extracted here -}
getTypeAndMorAux :: LogicGraph -> DGraph -> G_sign -> XLink
                 -> ResultT IO (G_sign, DGLinkType)
getTypeAndMorAux lg dg sg@(G_sign slid _ _) xLk = let
  emptySig = G_sign slid (ext_empty_signature slid) startSigId
  mkRtVAL sg' tp = return (sg', tp)
  cc = cons xLk
  in case edgeTypeModInc $ lType xLk of
    HidingDef -> mkRtVAL sg HidingDefLink
    GlobalDef -> mkRtVAL sg $ localOrGlobalDef Global cc
    HetDef -> mkRtVAL sg $ localOrGlobalDef Global cc
    LocalDef -> mkRtVAL sg $ localOrGlobalDef Local cc
    FreeOrCofreeDef fc -> do
      (sg', mNd) <- case mr_source xLk of
        Nothing -> return (emptySig, EmptyNode $ Logic slid)
        Just ms -> do
          (j, sg') <- signOfNode ms dg
          return (sg', JustNode $ NodeSig j sg')
      mkRtVAL sg' $ FreeOrCofreeDefLink fc mNd
    ThmType thTp prv _ _ -> let
      lStat = if not prv then LeftOpen
          else Proven (rule xLk) $ prBasis xLk in
      case thTp of
        HidingThm -> do
          (i', sg') <- case mr_source xLk of
            Just ms -> signOfNode ms dg
            Nothing -> Fail.fail "no morphism source declaration for HidingThmLink"
          mr' <- liftR $ ginclusion lg sg' sg
          mkRtVAL sg' $ HidingFreeOrCofreeThm Nothing i' mr' lStat
        FreeOrCofreeThm fc -> do
            (i', sg') <- case mr_source xLk of
              Just ms -> signOfNode ms dg
              Nothing -> return (-1, emptySig)
            mr' <- liftR $ ginclusion lg sg' sg
            mkRtVAL sg' $ HidingFreeOrCofreeThm (Just fc) i' mr' lStat
        GlobalOrLocalThm sc _ -> mkRtVAL sg
          $ ScopedLink sc (ThmLink lStat) $ mkConsStatus cc

{- | Generates and inserts a new DGNodeLab with a startoff-G_theory, an Element
and the the DGraphs Global Annotations. The caller has to ensure that the
chosen nodeId is not used in dgraph. -}
insertNode :: HetcatsOpts -> LogicGraph -> Maybe G_theory -> XNode -> Graph.Node
  -> (DGraph, LibEnv) -> ResultT IO (G_theory, DGraph, LibEnv)
insertNode opts lg mGt xNd n (dg, lv) = do
  (lbl, lv') <- generateNodeLab opts lg mGt xNd (dg, lv)
  return (dgn_theory lbl, insNodeDG (n, lbl) dg, lv')

{- | generate nodelab with startoff-gtheory and xnode information (a new libenv
is returned in case it was extended due to reference node insertion) -}
generateNodeLab :: HetcatsOpts -> LogicGraph -> Maybe G_theory -> XNode
  -> (DGraph, LibEnv) -> ResultT IO (DGNodeLab, LibEnv)
generateNodeLab opts lg mGt xNd (dg, lv) = case xNd of
  -- Case #1: Reference Node
  XRef nm rfNd rfLb spc -> do
          (dg', lv') <- case Map.lookup (emptyLibName rfLb) lv of
            Just dg' -> return (dg', lv)
            Nothing -> loadRefLib opts rfLb lv
          (i, gt) <- case lookupUniqueNodeByName rfNd dg' of
              Just (i, lbl) -> case signOf $ dgn_theory lbl of
                G_sign lid sign sId -> return (i, noSensGTheory lid sign sId)
              Nothing -> Fail.fail $ "reference node " ++ rfNd ++ " was not found"
          (gt', _) <- parseSpecs gt nm dg spc
          let nInf = newRefInfo (emptyLibName rfLb) i
          return (newInfoNodeLab nm nInf gt', lv')
  -- Case #2: Regular Node
  XNode nm lN (hid, syb) spc cc -> do
        -- StartOff-Theory. Taken from LogicGraph for initial Nodes
        gt0 <- case mGt of
          Nothing -> fmap emptyTheory $ lookupLogic "generateNodeLab " lN lg
          Just gt -> return gt
        -- hidden symbols use a different parser
        gt1 <- if hid then parseHidden gt0 syb
                 else fmap fst $ parseSpecs gt0 nm dg syb
        (gt2, syb') <- parseSpecs gt1 nm dg spc
        -- the DGOrigin is also different for nodes with hidden symbols
        lOrig <- if hid then let
                syms = Set.difference (symsOfGsign $ signOf gt0)
                  $ symsOfGsign $ signOf gt2
                in return $ DGRestriction NoRestriction syms
          else do
            diffSig <- liftR $ homGsigDiff (signOf gt2) $ signOf gt0
            return $ DGBasicSpec Nothing diffSig syb'
        return (newInfoNodeLab nm (newConsNodeInfo lOrig cc) gt2, lv)

insertFirstNode :: HetcatsOpts -> LogicGraph -> XNode -> (DGraph, LibEnv)
  -> ResultT IO (DGraph, LibEnv)
insertFirstNode opts lg xNd p@(dg', _) = let n = getNewNodeDG dg' in do
  (_, dg, lv) <- insertNode opts lg Nothing xNd n p
  return (dg, lv)

parseHidden :: G_theory -> String -> ResultT IO G_theory
parseHidden gt s' = do
  gs <- liftR $ deleteHiddenSymbols s' $ signOf gt
  return $ case gs of
    G_sign lid sg sId -> noSensGTheory lid sg sId

parseSpecs :: G_theory -> NodeName -> DGraph -> String
           -> ResultT IO (G_theory, Set G_symbol)
parseSpecs gt' nm dg spec = let
          (response, msg) = extendByBasicSpec (globalAnnos dg) spec gt'
          in case response of
            Success gt'' _ smbs _ -> return (gt'', smbs)
            Failure _ -> Fail.fail $ "[ " ++ showName nm ++ " ]\n" ++ msg

loadRefLib :: HetcatsOpts -> String -> LibEnv -> ResultT IO (DGraph, LibEnv)
loadRefLib opts ln lv = do
          mPath <- lift $ findFileOfLibNameAux opts { intype = DgXml } ln
          case mPath of
            Just path -> do
              (ln', lv') <- readDGXmlR opts path lv
              return (lookupDGraph ln' lv', lv')
            _ -> Fail.fail $ "no file exists for reference library " ++ ln

-- | creates an entirely empty theory
emptyTheory :: AnyLogic -> G_theory
emptyTheory (Logic lid) =
  G_theory lid Nothing (ext_empty_signature lid) startSigId noSens startThId

{- | A Node is looked up via its name in the DGraph. Returns the nodes
signature, but only if one single node is found for the respective name.
Otherwise an error is thrown. -}
signOfNode :: String -> DGraph -> ResultT IO (Graph.Node, G_sign)
signOfNode nd dg = case lookupUniqueNodeByName nd dg of
  Nothing -> Fail.fail $ "required node [" ++ nd ++ "] was not found in DGraph!"
  Just (j, lbl) ->
    return (j, signOf (dgn_theory lbl))
