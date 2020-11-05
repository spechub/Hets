{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module PGIP.GraphQL (isGraphQL, processGraphQL) where

import PGIP.GraphQL.Resolver

import PGIP.Shared

import Driver.Options

import Data.Aeson as Aeson
import qualified Data.ByteString.Lazy as LBS
import qualified Data.Text.Lazy.Encoding as LEncoding
import Data.Maybe
import qualified Data.HashMap.Lazy as Map
import qualified Data.Map as PlainMap
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
  let bodyQueryE = Aeson.eitherDecode $ LBS.fromStrict body :: Either String QueryBodyAux
  queryBody <- case bodyQueryE of
    Left message -> fail ("bad request body: " ++ message)
    Right b -> return $ toGraphQLQueryBody b
  resolve opts sessionReference (graphQLQuery queryBody) (graphQLVariables queryBody)

-- This structure contains the data that is passed to the GraphQL API
data QueryBody = QueryBody { graphQLQuery :: Text
                           , graphQLVariables :: PlainMap.Map Text Text
                           } deriving (Show, Generic)

-- This is an auxiliary strucutre that helps to parse the request body.
-- It is then converted to QueryBody.
data QueryBodyAux = QueryBodyAux { query :: Text
                                 , variables :: Maybe (PlainMap.Map Text Aeson.Value)
                                 } deriving (Show, Generic)
instance FromJSON QueryBodyAux


-- For an unknown reason, GraphQL-API requires the query to be enclosed in {}
toGraphQLQueryBody :: QueryBodyAux -> QueryBody
toGraphQLQueryBody QueryBodyAux { query = q, variables = aesonVariables } =
  QueryBody { graphQLQuery = q
            , graphQLVariables = PlainMap.map convert $
                                           fromMaybe PlainMap.empty aesonVariables
            }
  where
    convert = LText.toStrict . LEncoding.decodeUtf8 . Aeson.encode
