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
import Static.FromXmlUtils
import Static.XGraph

import Common.LibName
import Common.Result (Result (..))
import Common.ResultT

import Comorphisms.LogicGraph (logicGraph)

import Control.Monad.Trans (lift)
import Control.Monad (foldM, unless)

import qualified Data.Graph.Inductive.Graph as Graph (Node)
import qualified Data.Map as Map (lookup, insert, empty)
import Data.Set (Set)
import qualified Data.Set as Set

import Driver.Options
import Driver.ReadFn (findFileOfLibNameAux)

import Logic.ExtSign (ext_empty_signature)
import Logic.Grothendieck
import Logic.Logic (AnyLogic (..), cod, composeMorphisms)
import Logic.Prover (noSens)

import Text.XML.Light

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
  case (length xml', parseXMLDoc xml') of
    (l, Just xml) | l > 0 -> do
      xg <- liftR $ xGraph xml
      res <- rebuiltDG opts logicGraph xg lv
      let ln = libName xg
      return (ln, computeLibEnvTheories $ uncurry (Map.insert ln) res)
    _ -> fail $ "failed to parse XML file: " ++ path

{- | reconstructs the Development Graph via a previously created XGraph-
structure. -}
rebuiltDG :: HetcatsOpts -> LogicGraph -> XGraph -> LibEnv
          -> ResultT IO (DGraph, LibEnv)
rebuiltDG opts lg (XGraph _ thmLk body) lv = do
  res <- rebuiltBody body lv
  foldM (flip $ insertThmLink lg) res thmLk where
    rebuiltBody bd lv' = case bd of
        Root nds dg' -> do
          foldM (flip $ insertNode opts lg Nothing) (dg', lv') nds
        Branch nd lKs bd' -> do
          res0 <- rebuiltBody bd' lv'
          insertStep opts lg nd lKs res0

-- | inserts a new node as well as all definition links pointing at that node
insertStep :: HetcatsOpts -> LogicGraph -> XNode -> [XLink] -> (DGraph, LibEnv)
           -> ResultT IO (DGraph, LibEnv)
insertStep opts lg xNd lks (dg, lv) = do
  mrs <- mapM (getTypeAndMorphism lg dg) lks
  gsig <- do
    unless (length lks > 0) $ fail "insertStep: empty link list"
    case edgeTypeModInc $ lType $ head lks of
      FreeOrCofreeDef _ -> fmap snd $ signOfNode (source $ head lks) dg
      _ -> liftR $ gsigManyUnion lg $ map (\ (_, m, _) -> cod m) mrs
  let gt = case gsig of
        G_sign lid sg sId -> noSensGTheory lid sg sId
  (dg', lv') <- insertNode opts lg (Just gt) xNd (dg, lv)
  (j, gsig2) <- signOfNode (showName $ nodeName xNd) dg'
  dg'' <- foldM ( \ dgR ((i, mr, tp), lk) -> do
            lkLab <- finalizeLink lg lk mr gsig2 tp
            return $ insEdgeAsIs (i, j, lkLab) dgR
            ) dg' $ zip mrs lks
  return (dg'', lv')

-- | inserts a theorem link
insertThmLink :: LogicGraph -> XLink -> (DGraph, LibEnv)
               -> ResultT IO (DGraph, LibEnv)
insertThmLink lg xLk (dg, lv) = do
  (i, mr, tp) <- getTypeAndMorphism lg dg xLk
  (j, gsig) <- signOfNode (target xLk) dg
  lkLab <- finalizeLink lg xLk mr gsig tp
  return (insEdgeAsIs (i, j, lkLab) dg, lv)

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

-- | gathers information for an XLink using its source nodes signature
getTypeAndMorphism :: LogicGraph -> DGraph -> XLink
                   -> ResultT IO (Graph.Node, GMorphism, DGLinkType)
getTypeAndMorphism lg dg xLk = do
  (i, sg1) <- signOfNode (source xLk) dg
  (sg2, lTp) <- getTypeAndMorAux lg dg sg1 xLk
  mr' <- liftR $ getGMorphism lg sg2 (mr_name xLk) (mapping xLk)
  return (i, mr', lTp)

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
            Nothing -> fail "no morphism source declaration for HidingThmLink"
          mr' <- liftR $ ginclusion lg sg' sg
          mkRtVAL sg' $ HidingFreeOrCofreeThm Nothing i' mr' lStat
        FreeOrCofreeThm fc -> do
            (i', sg') <- case mr_source xLk of
              Just ms -> signOfNode ms dg
              Nothing -> return ((-1), emptySig)
            mr' <- liftR $ ginclusion lg sg' sg
            mkRtVAL sg' $ HidingFreeOrCofreeThm (Just fc) i' mr' lStat
        GlobalOrLocalThm sc _ -> mkRtVAL sg
          $ ScopedLink sc (ThmLink lStat) $ mkConsStatus cc

{- | Generates and inserts a new DGNodeLab with a startoff-G_theory, an Element
and the the DGraphs Global Annotations -}
insertNode :: HetcatsOpts -> LogicGraph -> Maybe G_theory -> XNode
           -> (DGraph, LibEnv) -> ResultT IO (DGraph, LibEnv)
insertNode opts lg mGt xNd (dg, lv) = case xNd of
  -- Case #1: Reference Node
  XRef nm rfNd rfLb spc -> do
          (dg', lv') <- case Map.lookup (emptyLibName rfLb) lv of
            Just dg' -> return (dg', lv)
            Nothing -> loadRefLib opts rfLb lv
          (i, gt) <- case lookupNodeByName rfNd dg' of
              [(i, lbl)] -> case signOf $ dgn_theory lbl of
                G_sign lid sign sId -> return (i, noSensGTheory lid sign sId)
              _ -> fail $ "reference node " ++ rfNd ++ " was not found"
          (gt', _) <- parseSpecs gt nm dg spc
          let n = getNewNodeDG dg
              nInf = newRefInfo (emptyLibName rfLb) i
              lbl = newInfoNodeLab nm nInf gt'
          return (addToRefNodesDG n nInf $ insLNodeDG (n, lbl) dg, lv')
  -- Case #2: Regular Node
  XNode nm lN (hid, syb) spc -> do
        -- StartOff-Theory. Taken from LogicGraph for initial Nodes
        gt0 <- case mGt of
          Nothing -> fmap emptyTheory $ lookupLogic "logic was not found" lN lg
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
        let lbl = newNodeLab nm lOrig gt2
        return (insLNodeDG (getNewNodeDG dg, lbl) dg, lv)

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
            Failure _ -> fail $ "[ " ++ showName nm ++ " ]\n" ++ msg

loadRefLib :: HetcatsOpts -> String -> LibEnv -> ResultT IO (DGraph, LibEnv)
loadRefLib opts ln lv = do
          mPath <- lift $ findFileOfLibNameAux opts { intype = DgXml } ln
          case mPath of
            Just path -> do
              (ln', lv') <- readDGXmlR opts path lv
              return (lookupDGraph ln' lv', lv')
            _ -> fail $ "no file exists for reference library " ++ ln

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
