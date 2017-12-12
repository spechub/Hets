{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module PGIP.GraphQL (isGraphQL, processGraphQL) where
import Debug.Trace

import PGIP.GraphQL.Handler

import PGIP.Shared

import Driver.Options

import Data.Aeson as Aeson
import qualified Data.ByteString.Lazy as LBS
import qualified Data.Text.Lazy.Encoding as LEncoding
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Text.Lazy as LText
import Data.Text as Text (Text, cons, snoc)
import GraphQL
import GraphQL.Value.ToValue (ToValue(..), toValue)
import Network.Wai
import GHC.Generics

isGraphQL :: String -> [String] -> Bool
isGraphQL httpVerb pathComponents =
  httpVerb == "POST" && pathComponents == ["graphql"]

processGraphQL :: HetcatsOpts -> Cache -> Request -> IO ResponseReceived
processGraphQL opts sessionReference request = do
  body <- receivedRequestBody request
  let bodyQueryE = Aeson.eitherDecode $ LBS.fromStrict body :: Either String QueryBody
  queryBody <- case bodyQueryE of
    Left message -> fail ("bad request body: " ++ message)
    Right b -> return $ toGraphQLQueryBody b
  trace "" $ trace "-----------------------------------" $ trace "" $ return ()
  trace "" $ trace (show queryBody) $ return ()
  trace "" $ trace "query:" $ trace (show $ queryGQL queryBody) $ return ()
  trace "" $ trace "variables:" $ trace (show $ variablesGQL queryBody) $ trace "" $ return ()

  -- result <- resultTest sessionReference "query document(location: \"input-location\") { fileVersion {path, evaluationState} locId}"
  result <- resultTest opts sessionReference (queryGQL queryBody) (variablesGQL queryBody)
  trace "" $ trace "result:" $ trace result $ trace "" $ return ()
  fail "got to the end"

-- This structure contains the data that is passed to the GraphQL API
data GraphQLQueryBody = GraphQLQueryBody { queryGQL :: Text
                                         , variablesGQL :: Map String GraphQL.Value
                                         } deriving Show

-- This is an auxiliary strucutre that helps to parse the request body.
-- It is then converted to GraphQLQueryBody.
data QueryBody = QueryBody { query :: Text
                           , variables :: Maybe (Map String Aeson.Value)
                           } deriving (Show, Generic)
instance FromJSON QueryBody

-- For an unknown reason, GraphQL-API requires the query to be enclosed in {}
toGraphQLQueryBody :: QueryBody -> GraphQLQueryBody
toGraphQLQueryBody QueryBody { query = q, variables = aesonVariables } =
  GraphQLQueryBody { queryGQL = Text.cons '{' $ Text.snoc q '}'
                   , variablesGQL = Map.map convert $
                                      fromMaybe Map.empty aesonVariables
                   }
  where
    convert = toValue . LText.toStrict . LEncoding.decodeUtf8 . Aeson.encode
