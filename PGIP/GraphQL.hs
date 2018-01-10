{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module PGIP.GraphQL (isGraphQL, processGraphQL) where

import PGIP.GraphQL.Resolver
import PGIP.GraphQL.Shared

import PGIP.Shared

import Driver.Options

import Data.Aeson as Aeson
import qualified Data.ByteString.Lazy as LBS
import qualified Data.Text.Lazy.Encoding as LEncoding
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Text.Lazy as LText
import Data.Text as Text
import Network.Wai
import GHC.Generics

isGraphQL :: String -> [String] -> Bool
isGraphQL httpVerb pathComponents =
  httpVerb == "POST" && pathComponents == ["graphql"]

processGraphQL :: HetcatsOpts -> Cache -> Request -> IO String
processGraphQL opts sessionReference request = do
  body <- receivedRequestBody request
  let bodyQueryE = Aeson.eitherDecode $ LBS.fromStrict body :: Either String QueryBodyTemp
  queryBody <- case bodyQueryE of
    Left message -> fail ("bad request body: " ++ message)
    Right b -> return $ toGraphQLQueryBody b
  queryType <- determineQueryType $ graphQLQuery queryBody
  resolve opts sessionReference queryType (graphQLQuery queryBody) (graphQLVariables queryBody)

determineQueryType :: Text -> IO QueryType
determineQueryType queryArg
  | isQueryPrefix "query DGraph" = return DGraph
  | isQueryPrefix "query OMS" = return OMS
  | isQueryPrefix "query Serialization" = return Serialization
  | isQueryPrefix "query SignatureMorphism" = return SignatureMorphism
  | isQueryPrefix "query Signature" = return Signature
  | otherwise =
      fail ("Query not supported.\n"
            ++ "The query must begin with \"query X\", where X is one of "
            ++ "DGraph, OMS, Serialization, Signature, SignatureMorphism\n"
            ++ "This is due to a limitation of only mimicking a GraphQL API.")
  where
    isQueryPrefix :: String -> Bool
    isQueryPrefix s = Text.isPrefixOf (Text.pack s) queryArg

-- This structure contains the data that is passed to the GraphQL API
data QueryBody = QueryBody { graphQLQuery :: Text
                           , graphQLVariables :: Map Text Text
                           } deriving (Show, Generic)

-- This is an auxiliary strucutre that helps to parse the request body.
-- It is then converted to GraphQLQueryBody.
data QueryBodyTemp = QueryBodyTemp { query :: Text
                                   , variables :: Maybe (Map Text Aeson.Value)
                                   } deriving (Show, Generic)
instance FromJSON QueryBodyTemp


-- For an unknown reason, GraphQL-API requires the query to be enclosed in {}
toGraphQLQueryBody :: QueryBodyTemp -> QueryBody
toGraphQLQueryBody QueryBodyTemp { query = q, variables = aesonVariables } =
  QueryBody { graphQLQuery = q
            , graphQLVariables = Map.map convert $
                                          fromMaybe Map.empty aesonVariables
            }
  where
    convert = LText.toStrict . LEncoding.decodeUtf8 . Aeson.encode
