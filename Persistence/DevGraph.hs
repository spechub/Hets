{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE QuasiQuotes                #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}

{- |
Module      :  ./Persistence.DevGraph.hs
Copyright   :  (c) Uni Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional
Portability :  portable
-}

-- #####################
-- HINT: look at Static.ToJson and Static.ToXml
-- this will give detailed information about how to extract
-- the relevant information from a development graph
-- #####################

module Persistence.DevGraph (exportLibEnv) where

import Persistence.Database
import Persistence.DBConfig
import Persistence.Schema

import Control.Monad (when)
import Database.Persist
import Database.Persist.Sql

import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.Trans.Reader (ReaderT)

import Static.DevGraph
import Static.DgUtils
import Common.LibName
import qualified Data.Map as Map
import Data.Graph.Inductive.Graph as Graph
import Data.Maybe
import Data.Text (pack)

type DBMonad backend m a = ReaderT backend m a
type DGName = LibName

exportLibEnv :: DBConfig -> LibEnv -> IO ()
exportLibEnv dbConfig lenv = onDatabase dbConfig $ do
    when (adapter dbConfig == Just "sqlite") $ runMigration migrateAll
    sequence $ Map.foldlWithKey exportAux [] lenv
    return ()
    where exportAux list dgname dgraph =
             exportDG dgname dgraph : list

exportDG :: (BaseBackend backend ~ SqlBackend, MonadIO m,
              PersistStoreWrite backend)
         => DGName -> DGraph -> DBMonad backend m ()
exportDG dgname dgraph = do
  let dg = dgBody dgraph
      nds = nodes dg
  graphId <- insert $ Graphs $ pack $ show dgname
  mapM_ (\n -> insert $ Nodes graphId $
                pack $ show $ getName $ dgn_name $ fromJust $ lab dg n) nds
  return ()
