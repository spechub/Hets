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

import Data.Graph.Inductive.Graph (Node)
import qualified Data.List as List (nub)
import qualified Data.Set as Set
import qualified Data.Map as Map

import Text.XML.Light hiding (Node)

dgXUpdate :: HetcatsOpts -> String -> LibEnv -> LibName -> DGraph
  -> ResultT IO (LibName, LibEnv)
dgXUpdate opts xs le ln dg = do
  (xml, chL) <- liftR $ changeXml (dGraph le ln dg) xs
  lift $ writeVerbFile opts (libNameToFile ln ++ ".xml")
    $ ppTopElement $ cleanUpElem xml
--  rebuiltDgXml opts le xml
  updateDG opts xml chL dg le

{- TODO (general): a lot of unused information is created. possibly check if
update is required for an element BEFORE processing xgraph information. -}
{- TODO (general): use ChangeGraph functions instead of DevGraph ones for
insertion? (called through FromXml) -}
{- TODO (general): determine the EXACT required change for each object instead
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

{- | move along xgraph structure and update or insert when required. updated
elements are those initially marked as such in changelist as well as all
elements that are subject to an ingoing signature modification. -}
iterateXgBody :: HetcatsOpts -> XGraph -> LibEnv -> DGraph
              -> ChangeList -> ResultT IO (DGraph, LibEnv, ChangeList)
iterateXgBody opts xgr lv dg chL = let lg = logicGraph in do
  rs1 <- foldM (mkNodeUpdate opts lg Nothing) (dg, lv, chL) $ startNodes xgr
  rs2 <- foldM (foldM (mkXStepUpdate opts lg)) rs1 $ reverse $ xg_body xgr
  mkThmLinkUpdates lg rs2 $ thmLinks xgr

{- | apply updates to one branch of the xgraph. -}
mkXStepUpdate :: HetcatsOpts -> LogicGraph -> (DGraph, LibEnv, ChangeList)
              -> ([XLink], XNode) -> ResultT IO (DGraph, LibEnv, ChangeList)
mkXStepUpdate opts lg (dg, lv, chL) (xlks, xnd) = let
  -- TODO by adjusting this test, the partial update can get more precise
  needSigUpd = foldl (\ r xlk -> r || maybe False (\_ -> True)
    (Map.lookup (parseNodeName $ source xlk) $ changedInDg chL)) False xlks
  {- TODO use ChangeGraph.setSignature when possible to keep old node info. -} 
  chL' = if needSigUpd then chL
         else updateNodeChange (nodeName xnd) (MkUpdate symMod) chL in do
    mrs <- mapM (getTypeAndMorphism lg dg) xlks
    G_sign lid sg sId <- getSigForXNode lg dg mrs
    rs1 <- mkNodeUpdate opts lg (Just $ noSensGTheory lid sg sId)
        (dg, lv, chL') xnd
    foldM (mkLinkUpdate lg) rs1 mrs

{- | check one xlink and make update or insertion to dg if required -}
mkLinkUpdate :: LogicGraph -> (DGraph, LibEnv, ChangeList)
             -> (Node, GMorphism, DGLinkType, XLink)
             -> ResultT IO (DGraph, LibEnv, ChangeList)
mkLinkUpdate lg (dg, lv, chL) lkMr@(_, _, _, xlk) = let
  -- TODO use setMorphism if possible to keep old link data
  mkLinkUpdateAux = case lookupUniqueNodeByName (target xlk) dg of
        Nothing -> fail $
          "required node [" ++ target xlk ++ "] was not found in DGraph!"
        Just (j, lbl) -> do
          dg' <- (insertLink lg j $ signOf $ dgn_theory lbl) dg lkMr
          return (dg', lv, chL { changeLinks = Map.delete (edgeId xlk)
            $ changeLinks chL })
  in case Map.lookup (edgeId xlk) $ changeLinks chL of
    -- TODO do we need to delete link first if updating an existing one??
    Just _ -> mkLinkUpdateAux
    {- even if the link is not marked for update, a gmorphism change might be 
    equired -}
    Nothing -> let hasThUpd s = maybe False (\ _ -> True)
                     $ Map.lookup (parseNodeName s) $ changedInDg chL in do
      if hasThUpd (source xlk) || hasThUpd (target xlk) then mkLinkUpdateAux
        else return (dg, lv, chL)

-- | updates any necessary ThmLinks
mkThmLinkUpdates :: LogicGraph -> (DGraph, LibEnv, ChangeList) -> [XLink]
                 -> ResultT IO (DGraph, LibEnv, ChangeList)
mkThmLinkUpdates lg (dg, lv, chL) xlks = do
  mrs <- mapM (getTypeAndMorphism lg dg) xlks
  -- TODO use setMorphism if possible to keep old link data
  foldM (mkLinkUpdate lg) (dg, lv, chL) mrs
  
{- | update or insert a node in accordance with XGraph data ONLY if the element
is marked for updating in changelist. -}
mkNodeUpdate :: HetcatsOpts -> LogicGraph -> Maybe G_theory
             -> (DGraph, LibEnv, ChangeList) -> XNode
             -> ResultT IO (DGraph, LibEnv, ChangeList)
mkNodeUpdate opts lg mGt (dg, lv, chL) xnd = let nm = nodeName xnd in
  case Map.lookup nm $ changeNodes chL of
    -- no change required, move on
    Nothing -> return (dg, lv, chL)
    Just MkInsert -> do
      (_, dg', lv') <- insertNode opts lg mGt xnd (getNewNodeDG dg) (dg, lv)
      return (dg', lv', chL { changeNodes = Map.delete nm $ changeNodes chL
                 -- TODO: the exact NodeMod could be calculated here!
                 , changedInDg = Map.insert nm symMod $ changedInDg chL })
    Just (MkUpdate nmod) -> do -- TODO: what if reference node??
      (j, dg'') <- liftR $ deleteNode dg nm
      (_, dg', lv') <- insertNode opts lg mGt xnd j (dg'', lv)
      return (dg', lv', chL { changeNodes = Map.delete nm $ changeNodes chL
                 -- TODO: the exact NodeMod could be calculated here!
                 , changedInDg = Map.insert nm symMod $ changedInDg chL })

{- | deletes the those elements from dgraph that are marked for deletion in
changelist. for link deletion, the affected nodes are marked as such in chL -}
deleteElements :: DGraph -> ChangeList -> Result (DGraph, ChangeList)
deleteElements dg0 chL0 = do
  (dg1, targets) <- foldM deleteLink (dg0, []) $ Set.toList $ deleteLinks chL0
  dg2 <- foldM (\ dg' -> fmap snd . deleteNode dg') dg1 $ Set.toList $ deleteNodes chL0
  chL' <- foldM (markNodeUpdates dg2) chL0 $ List.nub targets
  return (dg2, chL') where
    {- after deletion, all still-existing nodes which lost ingoing links must
    be marked for updating
    TODO: this might only be applicable to definition links. Ask Christian about it! -}
    markNodeUpdates dg chL trg = case lookupNodeWith ((== trg) . fst) dg of
      [] -> return chL
      [(_, lbl)] -> return
             $ updateNodeChange (dgn_name lbl) (MkUpdate symMod) chL
      _ -> fail $ "ambigous occurance of node #" ++ show trg

-- deletes a link from dg. returns smaller dg and (def)links target id
deleteLink :: Monad m => (DGraph, [Node]) -> XLink -> m (DGraph, [Node])
deleteLink (dg, tars) xlk = case lookupUniqueNodeByName (source xlk) dg of
  Just (s, _) -> let dg' = delEdgeDG s (edgeId xlk) dg
    in if not $ isDefEdgeType (lType xlk)
      then return (dg', tars)
      else case lookupUniqueNodeByName (target xlk) dg of
        Just (t, _) -> return (dg', t : tars)
        Nothing -> fail $ "required target [" ++ target xlk
          ++ "] was not found in DGraph!"
  Nothing -> fail $ "required source [" ++ source xlk
    ++ "] was not found in DGraph!"

-- deletes a node from dg
deleteNode :: Monad m => DGraph -> NodeName -> m (Node, DGraph)
deleteNode dg nm = let nd = showName nm
      in case lookupUniqueNodeByName nd dg of
        Just (j, _) -> let dg' = delNodeDG j dg in return (j, dg')
        Nothing -> fail $
          "required node [" ++ nd ++ "] was not found in DGraph!"

