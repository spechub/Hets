{- |
Module      :  $Header$
Description :  apply xupdate changes to a development graph
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

adjust development graph according to xupdate information
-}

module Static.ApplyChanges (dgXUpdate) where

import Static.ComputeTheory (computeLibEnvTheories)
import Static.DevGraph
import Static.GTheory
import Static.DgUtils
import Static.FromXml
import Static.History (undoAllChanges)
import Static.ToXml
import Static.XGraph
import Static.XSimplePath

import Driver.Options
import Driver.ReadFn (libNameToFile)
import Driver.WriteFn (writeVerbFile)

import Comorphisms.LogicGraph (logicGraph)

import Common.LibName
import Common.ResultT
import Common.Result
import Common.XUpdate

import Logic.Grothendieck

import Control.Monad
import Control.Monad.Trans (lift)

import Data.Graph.Inductive.Graph (Node, match, lab)
import qualified Data.List as List (nub)
import qualified Data.Set as Set
import qualified Data.Map as Map

import Text.XML.Light hiding (Node)

dgXUpdate :: HetcatsOpts -> String -> LibEnv -> LibName -> DGraph
  -> ResultT IO (LibName, LibEnv)
dgXUpdate opts xs le ln dg = do
  (xml, chL) <- liftR $ changeXml (dGraph le ln $ undoAllChanges dg) xs
  lift $ writeVerbFile opts (libNameToFile ln ++ ".xml")
    $ ppTopElement $ cleanUpElem xml
-- rebuiltDgXml opts le xml
  updateDG opts xml chL dg le

{- TODO (general): a lot of unused information is created. possibly check if
update is required for an element BEFORE processing xgraph information.
TODO (general): determine the EXACT required change for each object instead
of overwriting the existing one every time! -}

{- | updates a dgraph partially in accordance with changelist data from a .diff
application. an xgraph is created and used as a guideline for signature-
hierachy and for retrieving required new data. -}
updateDG :: HetcatsOpts -> Element -> ChangeList -> DGraph -> LibEnv
         -> ResultT IO (LibName, LibEnv)
updateDG opts xml chL dg le = do
  (dg', chL') <- liftR $ deleteElements dg chL
  xgr <- liftR $ xGraph xml
  let dg'' = dg' { globalAnnos = if updateAnnotations chL' then globAnnos xgr
                     else globalAnnos dg', getNewEdgeId = nextLinkId xgr }
  (dgFin, le', _) <- iterateXgBody opts xgr le dg'' chL'
  let ln = libName xgr
  -- TODO possibly test if any updates are left undone (corrupted dg/diff)
  return (ln, computeLibEnvTheories $ Map.insert ln dgFin le')

{- | move along xgraph structure and make updates or insertions in accordance
with changelist. In addition to the initial entries of the changelist, all
nodes that were subject to ingoing signature changes as well as all links
adjacent to an updated node will also be updated. -}
iterateXgBody :: HetcatsOpts -> XGraph -> LibEnv -> DGraph
              -> ChangeList -> ResultT IO (DGraph, LibEnv, ChangeList)
iterateXgBody opts xgr lv dg chL = let lg = logicGraph in do
  rs1 <- foldM (mkNodeUpdate opts lg Nothing) (dg, lv, chL) $ startNodes xgr
  rs2 <- foldM (foldM (mkXStepUpdate opts lg)) rs1 $ reverse $ xg_body xgr
  mkThmLinkUpdates lg rs2 $ thmLinks xgr

-- | apply updates to one branch of the xgraph.
mkXStepUpdate :: HetcatsOpts -> LogicGraph -> (DGraph, LibEnv, ChangeList)
              -> ([XLink], XNode) -> ResultT IO (DGraph, LibEnv, ChangeList)
mkXStepUpdate opts lg (dg, lv, chL) (xlks, xnd) = let
  -- first, add the req. signature change from ingoing definition links
  sigUpd = getLinkModUnion chL xlks
  chL' = if sigUpd == unMod then chL
    else updateNodeChange (MkUpdate sigUpd) (nodeName xnd) chL in do
    mrs <- mapM (getTypeAndMorphism lg dg) xlks
    G_sign lid sg sId <- getSigForXNode lg dg mrs
    rs1 <- mkNodeUpdate opts lg (Just $ noSensGTheory lid sg sId)
        (dg, lv, chL') xnd
    foldM (mkLinkUpdateAux lg) rs1 mrs

{- | the required node update due to link mods is derived using union.
predecessor signature changes have been collected through markLinkUpdates. -}
getLinkModUnion :: ChangeList -> [XLink] -> NodeMod
getLinkModUnion chL = foldr (\ xl ->
  case Map.lookup (edgeId xl) $ changeLinks chL of
    -- TODO get proper NodeMod here!
    Just MkInsert -> mergeNodeMod symMod
    Just (MkUpdate nmod) -> mergeNodeMod nmod
    Nothing -> id ) unMod

{- | update or insert a node in accordance with XGraph data ONLY if the element
is marked for updating in changelist. -}
mkNodeUpdate :: HetcatsOpts -> LogicGraph -> Maybe G_theory
             -> (DGraph, LibEnv, ChangeList) -> XNode
             -> ResultT IO (DGraph, LibEnv, ChangeList)
mkNodeUpdate opts lg mGt (dg, lv, chL) xnd = let nm = nodeName xnd in
  case Map.lookup nm $ changeNodes chL of
    -- no change required, move on
    Nothing -> return (dg, lv, chL)
    -- make insertion using FromXml.insertNode
    Just MkInsert -> do
      (_, dg', lv') <- insertNode opts lg mGt xnd (getNewNodeDG dg) (dg, lv)
      return (dg', lv', chL { changeNodes = Map.delete nm $ changeNodes chL })
    {- make update
    TODO: watch out for reference nodes!
    TODO: use NodeMod in a proper way, only update as much as necessary! -}
    Just (MkUpdate nmod) -> do
      (j, dg'') <- liftR $ deleteNode dg nm
      (_, dg', lv') <- insertNode opts lg mGt xnd j (dg'', lv)
      -- all adjacent links need to get their morphism updated
      let chL' = markLinkUpdates dg' j nmod chL
      return (dg', lv', chL' { changeNodes =
        Map.delete nm $ changeNodes chL' })

-- | mark all links adjacent to a node as update-pending
markLinkUpdates :: DGraph -> Node -> NodeMod -> ChangeList -> ChangeList
markLinkUpdates dg t nmod chL = let
  (Just (ins, _, _, outs), _) = match t $ dgBody dg
  in foldr (updateLinkChange (MkUpdate nmod)) chL
     $ map (dgl_id . fst) $ ins ++ outs

{- | gather target node information, call update-link, and delete link from
changelist after change application -}
mkLinkUpdateAux :: LogicGraph -> (DGraph, LibEnv, ChangeList)
                -> (Node, GMorphism, DGLinkType, XLink)
                -> ResultT IO (DGraph, LibEnv, ChangeList)
mkLinkUpdateAux lg (dg, lv, chL) lkMr@(_, _, _, xl) = do
  (j, gs) <- signOfNode (target xl) dg
  dg' <- mkLinkUpdate lg j gs chL dg lkMr
  return (dg', lv, chL { changeLinks =
    Map.delete (edgeId xl) $ changeLinks chL })

-- | check one xlink and make update or insertion to dg if required
mkLinkUpdate :: LogicGraph -> Node -> G_sign -> ChangeList -> DGraph
             -> (Node, GMorphism, DGLinkType, XLink) -> ResultT IO DGraph
mkLinkUpdate lg j gs chL dg lkMr@(_, _, _, xl) =
  case Map.lookup (edgeId xl) $ changeLinks chL of
    Nothing -> return dg
    Just MkInsert -> insertLink lg j gs dg lkMr
    -- TODO use setMorphism if possible to keep old link data
    Just (MkUpdate nmod) -> do
      dg' <- deleteLink dg xl
      insertLink lg j gs dg' lkMr

-- | updates any necessary ThmLinks
mkThmLinkUpdates :: LogicGraph -> (DGraph, LibEnv, ChangeList) -> [XLink]
                 -> ResultT IO (DGraph, LibEnv, ChangeList)
mkThmLinkUpdates lg (dg, lv, chL) xlks = do
  mrs <- mapM (getTypeAndMorphism lg dg) xlks
  foldM (mkLinkUpdateAux lg) (dg, lv, chL) mrs

{- | deletes the those elements from dgraph that are marked for deletion in
changelist. for link deletion, the affected nodes are marked as such in chL -}
deleteElements :: DGraph -> ChangeList -> Result (DGraph, ChangeList)
deleteElements dg chL = do
  (dg1, targets) <- foldM deleteLinkAux (dg, []) $ Set.toList $ deleteLinks chL
  dg2 <- foldM (\ dg' -> liftM snd . deleteNode dg') dg1 $ Set.toList
          $ deleteNodes chL
  {- after deletion, all still-existing nodes which lost ingoing definition
  links must be marked for updating. -}
  chL' <- foldM (flip $ markNodeUpdates dg2) chL $ List.nub targets
  return (dg2, chL' { deleteNodes = Set.empty, deleteLinks = Set.empty })

-- | look for given node in dg and mark as update-pending in changelist
markNodeUpdates :: Monad m => DGraph -> Node -> ChangeList -> m ChangeList
markNodeUpdates dg trg = case lab (dgBody dg) trg of
  Nothing -> return
  -- TODO: here also, the NodeMod could be calculated
  Just lbl -> return . updateNodeChange (MkUpdate symMod) (dgn_name lbl)

-- | deletes a link from dg.
deleteLink :: Monad m => DGraph -> XLink -> m DGraph
deleteLink dg = liftM fst . deleteLinkAux (dg, [])

-- | additionally returns (def)links target id
deleteLinkAux :: Monad m => (DGraph, [Node]) -> XLink -> m (DGraph, [Node])
deleteLinkAux (dg, tars) xl = case lookupUniqueNodeByName (source xl) dg of
  Just (s, _) -> let dg' = delEdgeDG s (edgeId xl) dg
    in if not $ isDefEdgeType (lType xl)
      then return (dg', tars)
      else case lookupUniqueNodeByName (target xl) dg of
        Just (t, _) -> return (dg', t : tars)
        Nothing -> fail $ "required target [" ++ target xl
          ++ "] was not found in DGraph!"
  Nothing -> fail $ "required source [" ++ source xl
    ++ "] was not found in DGraph!"

-- | deletes a node from dg
deleteNode :: Monad m => DGraph -> NodeName -> m (Node, DGraph)
deleteNode dg nm = let nd = showName nm
      in case lookupUniqueNodeByName nd dg of
        Just (j, _) -> let dg' = delNodeDG j dg in return (j, dg')
        Nothing -> fail $
          "required node [" ++ nd ++ "] was not found in DGraph!"
