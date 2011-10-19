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

import Static.DevGraph
import Static.ChangeGraph
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
  rebuiltDgXml opts le xml
--  updateDG opts xml chL dg le

updateDG :: HetcatsOpts -> Element -> ChangeList -> DGraph -> LibEnv
         -> ResultT IO (LibName, LibEnv)
updateDG opts xml chL dg le = do
  (dg', chL') <- liftR $ deleteElements dg chL
  xgr <- liftR $ xGraph xml
  let dg'' = if updateAnnotations chL then dg' { globalAnnos = globAnnos xgr }
        else dg'
  (dgFin, le', chL'') <- iterateXgBody opts xgr le dg'' chL'
  let ln = libName xgr
  -- TODO update/insert Theorem Links
  -- TODO adjust nextLinkId etc..
  -- TODO possibly test if any updates are left undone (corrupted dg/diff)
  return (ln, Map.insert ln dgFin le')

-- !! ALWAYS DELETE PROCESSED ENTRIES FROM CHANGELIST
iterateXgBody :: HetcatsOpts -> XGraph -> LibEnv -> DGraph
              -> ChangeList -> ResultT IO (DGraph, LibEnv, ChangeList)
iterateXgBody opts xgr lv dg chL = let lg = logicGraph in do
  rs1 <- foldM (mkNodeUpdate opts lg Nothing) (dg, lv, chL) $ startNodes xgr
  foldM (foldM (mkXStepUpdate opts lg)) rs1 $ xg_body xgr

{- | apply updates to one branch of the xgraph. conducted updates are
  - all updates or insertions found in ChangeList
  - resulting theory changes of former updates (source of indoing deflinks -}
mkXStepUpdate :: HetcatsOpts -> LogicGraph -> (DGraph, LibEnv, ChangeList)
              -> ([XLink], XNode) -> ResultT IO (DGraph, LibEnv, ChangeList)
mkXStepUpdate opts lg (dg, lv, chL) (xlks, xnd) = let
  needSigUpd = foldl (\ r xlk -> r || maybe False (\_ -> True)
    (Map.lookup (parseNodeName $ source xlk) $ changedInDg chL)) False xlks
  {- TODO use ChangeGraph.setSignature when possible to keep old node info. -} 
  chL' = if needSigUpd then chL { changeNodes = Map.insert (nodeName xnd)
           MkUpdate $ changeNodes chL } else chL in do
    mrs <- mapM (getTypeAndMorphism lg dg) xlks
    G_sign lid sg sId <- getSigForXNode opts lg (dg, lv) mrs xnd
    rs1 <- mkNodeUpdate opts lg (Just $ noSensGTheory lid sg sId)
        (dg, lv, chL') xnd
    foldM (mkLinkUpdate opts lg) rs1 mrs

{- iterate one branches list of xlinks and make update/insertions to dg as
required -}
mkLinkUpdate :: HetcatsOpts -> LogicGraph -> (DGraph, LibEnv, ChangeList)
             -> (Node, GMorphism, DGLinkType, XLink)
             -> ResultT IO (DGraph, LibEnv, ChangeList)
mkLinkUpdate = undefined

{- | update or insert a node in accordance with XGraph data ONLY if the element
is marked for updating in changelist. -}
mkNodeUpdate :: HetcatsOpts -> LogicGraph -> Maybe G_theory
             -> (DGraph, LibEnv, ChangeList) -> XNode
             -> ResultT IO (DGraph, LibEnv, ChangeList)
mkNodeUpdate opts lg mGt (dg, lv, chL) xnd = let nm = nodeName xnd in
  case Map.lookup nm $ changeNodes chL of
    -- no change required, move on
    Nothing -> return (dg, lv, chL)
    Just _ -> do
      (_, _, dg', lv') <- insertNode opts lg mGt xnd (dg, lv)
      return (dg', lv', chL { changeNodes = Map.delete nm $ changeNodes chL
                 -- TODO: the exact NodeMod could be calculated here!
                 , changedInDg = Map.insert nm symMod $ changedInDg chL })

{- | deletes the those elements from dgraph that are marked for deletion in
changelist. for link deletion, the affected nodes are marked as such in chL -}
deleteElements :: DGraph -> ChangeList -> Result (DGraph, ChangeList)
deleteElements dg0 chL0 = do
  (dg1, targets) <- foldM deleteLink (dg0, []) $ Set.toList $ deleteLinks chL0
  dg2 <- foldM deleteNode dg1 $ Set.toList $ deleteNodes chL0
  chL' <- foldM (markNodeUpdates dg2) chL0 $ List.nub targets
  return (dg2, chL') where
    -- deletes a link from dg. returns smaller dg and links target id
    deleteLink (dg, tars) (trg, ei) = case lookupUniqueNodeByName trg dg of
      Just (j, _) -> liftM (\ dg' -> (dg', j : tars)) $ deleteDGLink j ei dg
      Nothing -> fail $
        "required target [" ++ trg ++ "] was not found in DGraph!"
    -- deletes a node from dg
    deleteNode dg nm = let nd = showName nm
      in case lookupUniqueNodeByName nd dg of
        Just (j, _) -> deleteDGNode j dg
        Nothing -> fail $
          "required node [" ++ nd ++ "] was not found in DGraph!"
    {- after deletion, all still-existing nodes which lost ingoing links must
    be marked for updating
    TODO: this might only be applicable to definition links. Ask Christian about it! -}
    markNodeUpdates dg chL trg = case lookupNodeWith ((== trg) . fst) dg of
      [] -> return chL
      [(_, lbl)] -> return $ chL
        { changeNodes = Map.insert (dgn_name lbl) MkUpdate $ changeNodes chL } 
      _ -> fail $ "ambigous occurance of node #" ++ show trg

