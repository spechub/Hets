{- |
Module      :  ./Static/ApplyChanges.hs
Description :  apply xupdate changes to a development graph
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

adjust development graph according to xupdate information
-}

module Static.ApplyChanges (dgXUpdateMods, dgXUpdate) where

import Static.ComputeTheory
import Static.DevGraph
import Static.DgUtils
import Static.FromXml
import Static.GTheory
import Static.History (undoAllChanges, changeDGH, clearHistory)
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
import qualified Control.Monad.Fail as Fail
import Control.Monad.Trans (lift)

import Data.Graph.Inductive.Graph (Node, match, lab)
import qualified Data.List as List (nub)
import qualified Data.Set as Set
import qualified Data.Map as Map

import Text.XML.Light hiding (Node)

{- incorporate a previous session (diff) upon an exising dgraph. The structure
is as follows:
 - roll back the current dg to it's initial state
 - apply diff to initial dg
 - create xgraph from dg'
 - incorporate changes into current dg; the xgraph serves for structuring.

NOTE: The data-type NodeMod holds information about the changes upon a node.
However, with the current usage, a Boolean value would do since the module only
knows update or don't-update. We kept the NodeMod-approach since proper usage
of the NodeMod data type might allow more precise updating.

NOTE(2): If any element changes, ALL elements that lie underneath in terms of
signature-hierachy will receive updating as well (even if two subsequent
changes would lead to an unchanged signature further down). -}

-- | recieves diff as a string and current dg and prepares those for processing
dgXUpdate :: HetcatsOpts -> String -> LibEnv -> LibName -> DGraph
          -> ResultT IO (LibName, LibEnv)
dgXUpdate opts xs le ln dg = case parseXMLDoc xs of
    Nothing -> fail "dgXUpdate: cannot parse xupdate file"
    Just diff -> let
      -- we assume that the diff refers to an unchanged dg..
      dgOld = undoAllChanges dg
      oldLId = getNewEdgeId dgOld
      xorig = dGraph opts le ln dgOld
      in dgXUpdateMods opts xorig oldLId diff le ln dg

{- | updates a dgraph partially in accordance with changelist data from a .diff
application. an xgraph is created and used as a guideline for signature-
hierachy and for retrieving required new data. -}
dgXUpdateMods :: HetcatsOpts -> Element -> EdgeId -> Element -> LibEnv
              -> LibName -> DGraph -> ResultT IO (LibName, LibEnv)
dgXUpdateMods opts xorig oldLId diff le ln dg = do
  -- dg with changes incorporated (diff only) and listing of these changes
  (xml, chL) <- liftR $ changeXmlMod xorig diff
  lift $ writeVerbFile opts (libNameToFile ln ++ ".xml")
    $ ppTopElement $ cleanUpElem xml
  xgr <- liftR $ xGraph xml
  -- the changes will now be incorporated in the so-far unchanged session-dg.
  (dg0, chL') <- liftR $ deleteElements dg chL
  let newLId = max (nextLinkId xgr) $ getNewEdgeId dg
      -- to anticipate multiple use of link-ids
      dg1 = renumberDGLinks oldLId newLId dg0
      dg2 = dg1 { globalAnnos = globAnnos xgr
                -- TODO as of now, ALL nodes will be removed from globalEnv!
                , globalEnv = Map.empty }
  (dg3, le', chL'') <- iterateXgBody opts xgr le dg2 chL'
  -- for any leftover theorem link updates, the respective links are deleted
  dgFin <- fmap clearHistory $ deleteLeftoverChanges dg3 chL''
  return (ln, computeLibEnvTheories $ Map.insert ln dgFin le')

{- | deletes theorem links from dg that were left-over in changelist.
fails if any other undone changes are found -}
deleteLeftoverChanges :: Fail.MonadFail m => DGraph -> ChangeList -> m DGraph
deleteLeftoverChanges dg chL = let lIds = Map.keys $ changeLinks chL in do
  unless (emptyChangeList == chL { changeLinks = Map.empty })
    $ Fail.fail $ "some changes could not be processed:\n" ++ show chL
  foldM (\ dg' ei -> case getDGLinksById ei dg' of
    [ledge@(_, _, lkLab)] | not $ isDefEdge $ dgl_type lkLab -> return
      $ changeDGH dg' $ DeleteEdge ledge
    _ -> fail $ "deleteLeftoverChanges: conflict with edge #" ++ show ei
    ) dg lIds

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
  chL' = if sigUpd == unMod then chL else updateNodeChange (MkUpdate sigUpd)
              (nodeName xnd) chL in do
    mrs <- mapM (getTypeAndMorphism lg dg) xlks
    G_sign lid sg sId <- getSigForXNode lg dg mrs
    rs1 <- mkNodeUpdate opts lg (Just $ noSensGTheory lid sg sId)
        (dg, lv, chL') xnd
    foldM (mkLinkUpdate lg) rs1 mrs

{- | the required node update due to link mods is derived using union.
predecessor signature changes have been collected through markLinkUpdates. -}
getLinkModUnion :: ChangeList -> [XLink] -> NodeMod
getLinkModUnion chL = foldr (\ xl ->
  case Map.lookup (edgeId xl) $ changeLinks chL of
    -- TODO: Cons symMod was chosen only to ensure updating of adjacent nodes.
    Just MkInsert -> mergeNodeMod symMod
    Just (MkUpdate nmod) -> mergeNodeMod nmod
    Nothing -> id ) unMod

{- | update or insert a node in accordance with XGraph data ONLY if the element
is marked for updating in changelist. -}
mkNodeUpdate :: HetcatsOpts -> LogicGraph -> Maybe G_theory
             -> (DGraph, LibEnv, ChangeList) -> XNode
             -> ResultT IO (DGraph, LibEnv, ChangeList)
mkNodeUpdate opts lg mGt (dg, lv, chL) xnd = let
  nm = nodeName xnd
  nd = showName nm in case retrieveNodeChange nm chL of
    -- no change required, move on
    Nothing -> return (dg, lv, chL)
    -- make insertion using DGChange.InsertNode object
    Just (MkInsert, chL') -> let n = getNewNodeDG dg in do
      (lbl, lv') <- generateNodeLab opts lg mGt xnd (dg, lv)
      let dg' = changeDGH dg $ InsertNode (n, lbl)
      return (dg', lv', chL')
    -- make update using DGChange.SetNodeLab object
    Just (MkUpdate nmod, chL') -> do
      (lbl, lv') <- generateNodeLab opts lg mGt xnd (dg, lv)
      (n, lblOrig) <- case lookupUniqueNodeByName nd dg of
        Just ndOrig -> return ndOrig
        Nothing -> fail $ "node [" ++ nd ++ "] was not found in dg, but was"
            ++ " marked for updating"
      let dg' = changeDGH dg $ SetNodeLab lblOrig (n, lbl)
      -- all adjacent links need to get their morphism updated
      return (dg', lv', markLinkUpdates dg' n nmod chL')

-- | mark all links adjacent to a node as update-pending
markLinkUpdates :: DGraph -> Node -> NodeMod -> ChangeList -> ChangeList
markLinkUpdates dg t nmod chL = let
  (Just (ins, _, _, outs), _) = match t $ dgBody dg
  in foldr (updateLinkChange (MkUpdate nmod) . dgl_id . fst) chL
     $ ins ++ outs

-- | update or insert a link if said so in changelist
mkLinkUpdate :: LogicGraph -> (DGraph, LibEnv, ChangeList)
             -> (Node, GMorphism, DGLinkType, XLink)
             -> ResultT IO (DGraph, LibEnv, ChangeList)
mkLinkUpdate lg (dg, lv, chL) (i, mr, tp, xl) = let ei = edgeId xl in
  case retrieveLinkChange ei chL of
    Nothing -> return (dg, lv, chL)
    Just (chA, chL') -> do
      (j, gs) <- signOfNode (target xl) dg
      lkLab <- finalizeLink lg xl mr gs tp
      -- if updating an existing link, the old one is deleted from dg first
      dg' <- if chA == MkInsert then return dg else
        fmap (changeDGH dg . DeleteEdge) $ lookupUniqueLink i ei dg
      return (changeDGH dg' $ InsertEdge (i, j, lkLab), lv, chL')

-- | updates any necessary ThmLinks
mkThmLinkUpdates :: LogicGraph -> (DGraph, LibEnv, ChangeList) -> [XLink]
                 -> ResultT IO (DGraph, LibEnv, ChangeList)
mkThmLinkUpdates lg (dg, lv, chL) xlks = do
  mrs <- mapM (getTypeAndMorphism lg dg) xlks
  foldM (mkLinkUpdate lg) (dg, lv, chL) mrs

{- | deletes those elements from dgraph that are marked for deletion in
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
markNodeUpdates :: Fail.MonadFail m => DGraph -> Node -> ChangeList -> m ChangeList
markNodeUpdates dg trg = case lab (dgBody dg) trg of
  Nothing -> return
  -- TODO: symMod was chosen to ensure updating, it does not always apply.
  Just lbl -> return . updateNodeChange (MkUpdate symMod) (dgn_name lbl)

-- | deletes a link from dg and returns (def)links target id additionally
deleteLinkAux :: Fail.MonadFail m => (DGraph, [Node]) -> XLink -> m (DGraph, [Node])
deleteLinkAux (dg, tars) xl = case lookupUniqueNodeByName (source xl) dg of
  Just (s, _) -> do
    dg' <- liftM (changeDGH dg . DeleteEdge)
        $ lookupUniqueLink s (edgeId xl) dg
    if not $ isDefEdgeType (lType xl)
      then return (dg', tars)
      else case lookupUniqueNodeByName (target xl) dg of
        Just (t, _) -> return (dg', t : tars)
        Nothing -> Fail.fail $ "required target [" ++ target xl
          ++ "] was not found in DGraph!"
  Nothing -> Fail.fail $ "required source [" ++ source xl
    ++ "] was not found in DGraph!"

-- | deletes a node from dg
deleteNode :: Fail.MonadFail m => DGraph -> NodeName -> m (Node, DGraph)
deleteNode dg nm = let nd = showName nm
  in case lookupUniqueNodeByName nd dg of
      Just (j, lbl) -> return (j, changeDGH dg $ DeleteNode (j, lbl))
      Nothing -> Fail.fail $
        "required node [" ++ nd ++ "] was not found in DGraph!"
