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

module Persistence.DevGraph where
       
import Control.Monad.IO.Class  (liftIO)
import Database.Persist
import Database.Persist.Sqlite
import Database.Persist.TH

import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.Logger (NoLoggingT)
import Control.Monad.Trans.Control (MonadBaseControl)
import Control.Monad.Trans.Reader (ReaderT)
import Control.Monad.Trans.Resource (ResourceT)

import Static.DevGraph
import Static.DgUtils
import Data.Text (Text, pack)
import Common.LibName
import qualified Data.Map as Map
import Data.Graph.Inductive.Graph as Graph
import Data.Maybe

share [mkPersist sqlSettings, mkMigrate "migrateAll"] [persistLowerCase|
Graphs
    name Text
    deriving Show
Nodes
    graphId GraphsId
    name Text
    deriving Show
Edges
    graphId GraphsId
    sourceId NodesId
    targetId NodesId
    deriving Show
|]

type DBMonad backend m a = ReaderT backend (NoLoggingT (ResourceT m)) a
type DGName = LibName

exportLibEnv :: String -> LibEnv -> IO ()
exportLibEnv db lenv = runSqlite (pack db) $ do
    runMigration migrateAll
    sequence $ Map.foldlWithKey exportAux [] lenv
    return ()
    where exportAux list dgname dgraph =
             exportDG dgname dgraph : list

exportDG :: (MonadIO m, IsSqlBackend backend, PersistQueryRead backend, PersistStoreWrite backend)	 
             => DGName -> DGraph -> DBMonad backend m ()
exportDG dgname dgraph = do
  let dg = dgBody dgraph
      nds = nodes dg
  graphId <- insert $ Graphs $ pack $ show dgname
  mapM_ (\n -> insert $ Nodes graphId $
                pack $ show $ getName $ dgn_name $ fromJust $ lab dg n) nds
  return ()
    
