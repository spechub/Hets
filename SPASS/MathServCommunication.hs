module SPASS.MathServCommunication where

import Text.XML.Serializer
import Org.Xmlsoap.Schemas.Soap.Envelope as ENV

import Data.Generics2
import Data.Typeable

data MathServServices = 
    ProveProblemOpt { in0 :: String
                    , in1 :: Int}
  | ProveProblemChoice { in0 :: String
                       , in1 :: Int}
  | ProveTPTPProblem { in0 :: String
                     , in1 :: Int}
  | ProveTPTPProblemWithOptions { in0 :: String
                                , in1 :: Int
                                , in2 :: String}
  | ProveProblem { in0 :: String
                 , in1 :: Int}

data MathServOutput = 
    ProveProblemOptResponse { 
          proveProblemOptReturn :: String } 
  | ProveProblemChoiceResponse { 
          proveProblemChoiceReturn :: String } 
  | ProveTPTPProblemResponse { 
          proveTPTPProblemReturn :: String } 
  | ProveTPTPProblemWithOptionsResponse { 
          proveTPTPProblemWithOptionsReturn :: String } 
  | ProveProblemResponse { 
          proveProblemReturn :: String } 
    deriving Show

instance XMLNamespace MathServServices
instance XMLNamespace MathServOutput


$(xmlify [''MathServServices] [])
$(xmlify [''MathServOutput] [capFieldsE])

getResponse :: MathServOutput -> String
getResponse mso = 
    case mso of
    ProveProblemOptResponse _ -> proveProblemOptReturn mso
    ProveProblemChoiceResponse _ -> proveProblemChoiceReturn mso
    ProveTPTPProblemResponse _ -> proveTPTPProblemReturn mso
    ProveProblemResponse _ -> proveProblemReturn mso
    ProveTPTPProblemWithOptionsResponse _ -> 
        proveTPTPProblemWithOptionsReturn mso

mkProveProblem :: Maybe String -- ^ extra options
               -> String -- ^ Service name 
               -> String -- ^ SOAP operation name
               -> String -> Int -> MathServServices
mkProveProblem mopts service operation = 
    case service of 
     "VampireService" -> 
         case operation of 
          "ProveTPTPProblem" -> maybe ProveTPTPProblem
                                      (\ opts -> \ x y -> 
                                          ProveTPTPProblemWithOptions x y opts)
                                      mopts
          "ProveProblem" -> ProveProblem
          _ -> fail $ "unknown Operation for service Broker\n"++
                  "known operations: ProveProblem, ProveTPTPProblem"
     "Broker" -> case operation of 
                 "ProveProblemOpt" -> ProveProblemOpt
                 "ProveProblemChoice" -> ProveProblemChoice
                 _ -> fail $ "unknown Operation for service Broker\n"++
                       "known operations: ProveProblemOpt, ProveProblemChoice"
     _ -> fail $ "unknown Service\nknown services: "++
                          "VampireService, Broker"

