{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module PGIP.GraphQL.Handler where
import Debug.Trace

import PGIP.GraphQL.Schema

import PGIP.Shared

import Driver.Options

import Data.Aeson as Aeson hiding (Object)
import qualified Data.ByteString.Lazy.Char8 as Char8 (unpack)
import Data.Char (chr)
import Data.IORef
import Data.List (find)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text (pack, unpack)
import GraphQL
import GraphQL.API (Object, Field, Argument, (:>), Union)
import GraphQL.Resolver (Handler, (:<>)(..), unionValue)
-- import Protolude hiding (head, map, show, trace, undefined)

resultTest :: HetcatsOpts -> Cache -> Text -> VariableValues -> IO String
resultTest opts cache queryString variables =
  fmap Char8.unpack $ Aeson.encode <$> queryTest opts cache queryString variables

queryTest :: HetcatsOpts -> Cache -> Text -> VariableValues -> IO Response
queryTest opts cache queryString variables =
  let Right schema = makeSchema @Query
  in  case compileQuery schema queryString of
        Left message -> fail $ show message
        Right compiledQuery ->
          executeQuery @Query (handleQuery opts cache) compiledQuery Nothing variables

handleQuery :: HetcatsOpts -> Cache -> Handler IO Query
handleQuery opts cache = pure $
  library opts cache

library :: HetcatsOpts -> Cache -> Text -> Handler IO Library
library opts cache location = do
  (_, sessMap) <- readIORef cache
  trace "" $ trace "sessMap" $ trace (show sessMap) $ return ()
  trace "" $ trace "keys sessMap" $ trace (show $ Map.keys sessMap) $ return ()
  trace "" $ trace "find location $ keys sessMap" $ trace (show $ find (\ l -> head l == Text.unpack location) $ Map.keys sessMap) $ return ()
  let sessionKeyM = find (\ l -> head l == Text.unpack location) $ Map.keys sessMap
  let sessionM = case sessionKeyM of
        Nothing -> Nothing
        Just key -> Map.lookup key sessMap
  case sessionM of
    -- TODO: check the database
    Nothing -> fail "TODO: ask database"
    Just session -> do
      let libEnv = sessLibEnv session
      let libName = sessLibName session
      pure $
        fileVersion opts cache location
        :<> locId
  where
    locId = pure location

fileVersion :: HetcatsOpts -> Cache -> Text -> Handler IO FileVersion
fileVersion opts cache location = pure $
  evaluationState
  :<> path
  where
    evaluationState = pure "finished_successfully"
    path = pure location
