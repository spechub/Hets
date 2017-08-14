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

module Persistence.Schema where

import Database.Persist.Sql
import Database.Persist.TH

import Data.Text (Text)

share [mkPersist sqlSettings, mkMigrate "migrateAll"] [persistLowerCase|
Graphs -- should become Document
    name Text
    deriving Show
Nodes -- should become OMS
    graphId GraphsId
    name Text
    deriving Show
Edges -- should become Mapping
    graphId GraphsId
    sourceId NodesId
    targetId NodesId
    deriving Show
|]
