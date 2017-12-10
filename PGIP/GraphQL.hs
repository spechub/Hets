module PGIP.GraphQL (isGraphQL, processGraphQL) where

import Debug.Trace

import PGIP.GraphQL.Schema

import PGIP.Shared

import Driver.Options

import Network.Wai

isGraphQL :: String -> [String] -> Bool
isGraphQL httpVerb pathComponents =
  -- TODO: Remove "True"
  True || httpVerb == "POST" && pathComponents == ["graphql"]

processGraphQL :: HetcatsOpts -> Cache -> Request -> IO ResponseReceived
processGraphQL opts sessionReference request = trace ("request: " ++ show request) $ do
  json <- jsonBody request
  trace (show json) undefined
