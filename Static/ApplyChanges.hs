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
import Static.DgUtils
import Static.FromXml
import Static.ToXml
import Static.XGraph
import Static.XSimplePath

import Driver.Options
import Driver.ReadFn (libNameToFile)
import Driver.WriteFn (writeVerbFile)

import Common.LibName
import Common.ResultT
import Common.Result
import Common.XUpdate

import Control.Monad
import Control.Monad.Trans (lift)

import qualified Data.Set as Set
import qualified Data.Map as Map

import Text.XML.Light

dgXUpdate :: HetcatsOpts -> String -> LibEnv -> LibName -> DGraph
  -> ResultT IO (LibName, LibEnv)
dgXUpdate opts xs le ln dg = do
  (xml, chL) <- liftR $ changeXml (dGraph le ln dg) xs
  lift $ writeVerbFile opts (libNameToFile ln ++ ".xml")
    $ ppTopElement $ cleanUpElem xml
  rebuiltDgXml opts le xml

updateDG :: HetcatsOpts -> Element -> ChangeList -> DGraph -> LibEnv
         -> ResultT IO (LibName, LibEnv)
updateDG opts xml chL dg le = liftR $ do
  (dg', chL') <- deleteElements dg chL
  xgr <- xGraph xml
  let dg'' = if updateAnnotations chL then dg' { globalAnnos = globAnnos xgr }
        else dg'
  dgFin <- iterateXgBody opts xgr le dg'' chL'
  let ln = libName xgr
  return (ln, Map.insert ln dgFin le) 

deleteElements :: DGraph -> ChangeList -> Result (DGraph, ChangeList)
deleteElements dg0 chL = let
    -- deletes a link from dg. returns smaller dg and links target id
    deleteLink (dg, tar) ei = case getDGLinksById ei dg of
      [] -> fail $ "required link [" ++ show ei ++ "] was not found in DGraph!"
      [(i, j, _)] -> do
        dg' <- deleteDGLink i j ei dg
        return (dg', j : tar)
      _ -> fail $ "ambigous occurance of linkId: " ++ show ei
    -- deletes a node from dg
    deleteNode dg nm = let nd = showName nm
      in case lookupUniqueNodeByName nd dg of
        Nothing -> fail $ "required node [" ++ nd ++ "] was not found in DGraph!"
        Just (j, _) -> deleteDGNode j dg
  in do
  (dg1, targets) <- foldM deleteLink (dg0, []) $ Set.toList $ deleteLinks chL
  dg2 <- foldM deleteNode dg1 $ Set.toList $ deleteNodes chL
  {- TODO: all target nodes should be looked up in dgraph AFTER node deletion.
  if they are gone, everything is fine. if not, they should be marked for
  updating (possibly just added to ChangeList) -}
  return (dg2, chL)

-- !! ALWAYS DELETE PROCESSED ENTRIES FROM DGEFFECT OBJECT
iterateXgBody :: Monad m => HetcatsOpts -> XGraph -> LibEnv -> DGraph
              -> ChangeList -> m DGraph
iterateXgBody = undefined
  -- check for adds/updates of initial nodes
  -- rebuilt/iterate body
  -- adjust nextLinkId etc.. then return

processBranch :: Monad m => [XLink] -> XNode -> DGraph -> ChangeList
              -> m (DGraph, Bool)
processBranch = undefined
  -- insert and update links
  -- insert or update node (use fromXml functions here)
  -- check if any changes made, then return
