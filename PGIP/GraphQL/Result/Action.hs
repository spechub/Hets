{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.Action where

import Data.Data

data Action = Action { evaluationState :: String
                     , message :: Maybe String
                     } deriving (Show, Typeable, Data)
