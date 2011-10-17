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
import Static.FromXml
import Static.ToXml
import Static.XGraph
import Static.XSimplePath

import Driver.Options
import Driver.ReadFn (libNameToFile)
import Driver.WriteFn (writeVerbFile)

import Common.LibName
import Common.ResultT
import Common.XUpdate

import Control.Monad.Trans (lift)
import Text.XML.Light

dgXUpdate :: HetcatsOpts -> String -> LibEnv -> LibName -> DGraph
  -> ResultT IO (LibName, LibEnv)
dgXUpdate opts xs le ln dg = do
  (xml, _) <- liftR $ changeXml (dGraph le ln dg) xs
  lift $ writeVerbFile opts (libNameToFile ln ++ ".xml")
    $ ppTopElement $ cleanUpElem xml
  rebuiltDgXml opts le xml

-- !! ALWAYS DELETE PROCESSED ENTRIES FROM DGEFFECT OBJECT
iterateXGraph :: Monad m => HetcatsOpts -> XGraph -> LibEnv -> DGraph
              -> ChangeList -> m DGraph
iterateXGraph = undefined
  -- delete nodes and links from dg
  -- (? rebuilt global annotation ?)
  -- check for adds/updates of initial nodes
  -- rebuilt/iterate body
  -- adjust nextLinkId etc.. then return

{- TODO add parameter for needsChange/Update. if True, update ALL DgElements
(using fromXml functionality). if False, only update from ChangeList. -}
iterateXTree :: Monad m => HetcatsOpts -> XTree -> LibEnv -> DGraph
             -> ChangeList -> m DGraph
iterateXTree opts xt lv dg _ = case xt of
  [] -> undefined
    -- when tree is null, check if any changes left. else return dg
  cur : r -> undefined
    -- process all branches
    {- scan for changes; call iterateXTree with updateTheory for those
    upcomming branches that have any changed nodes as source. 
    !! CAUTION: such branches may occur ANYWHERE within the remaining tree! -}

processBranch :: Monad m => [XLink] -> XNode -> DGraph -> ChangeList
              -> m (DGraph, Bool)
processBranch xlks xnd dg dgEff = undefined
  -- insert and update links
  -- insert or update node (use fromXml functions here)
  -- check if any changes made, then return
