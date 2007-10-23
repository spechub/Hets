{-# OPTIONS -fth #-}
module SoftFOL.MathServCommunication where

import Text.XML.Serializer
import Org.W3.N2001.XMLSchema ()

import Data.Generics2.Basics
import Data.Typeable

data MathServOperations =
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

instance XMLNamespace MathServOperations
instance XMLNamespace MathServOutput


$(xmlify [''MathServOperations] [])
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
