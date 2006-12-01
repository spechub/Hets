{-# OPTIONS -fth #-}
-- | simple test program that sends a file as soap message to a 
-- MathServ Broker and to other Services like Vampire

-- SPASS/tests/soapTest denebola 8080 Broker ProveProblemOpt SPASS/tests/asym.tptp 10

module Main where

import System.Environment (getArgs)
import System.IO
import System.Exit

import Network.URI
import Network.Service

import Text.XML.HXT.Aliases

import Text.XML.Serializer
import Org.Xmlsoap.Schemas.Soap.Envelope as ENV

import Data.Generics2
import Data.Typeable
import Data.List (intersperse)

import Control.Monad (mapM_)

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
     "Broker" -> case operation of 
                 "ProveProblemOpt" -> ProveProblemOpt
                 "ProveProblemChoice" -> ProveProblemChoice
                 _ -> fail $ "unknown Operation for service Broker\n"++
                       "known operations: ProveProblemOpt, ProveProblemChoice"
     x 
         | x `elem` services -> singleATP
         | otherwise -> fail $ "unknown Service\nknown services: "++
                          "Broker,"++concat (intersperse "," services)
    where singleATP =
           case operation of 
            "ProveTPTPProblem" -> maybe ProveTPTPProblem
                                      (\ opts -> \ x y -> 
                                          ProveTPTPProblemWithOptions x y opts)
                                      mopts
            "ProveProblem" -> ProveProblem
            _ -> fail $ "unknown Operation for service \""++service++"\"\n"++
                  "known operations: ProveProblem, ProveTPTPProblem"

services :: [String]
services = ["EService","SpassService","VampireService","WaldmeisterService",
            "ParadoxService","DctpService","OtterService"]

usage :: String -> IO ()
usage m = do hPutStrLn stderr $
                 "Usage: soapTest <server-name> <port> <service-name> "++
                 "<operation> <problem-file> <timeout> [<options>]\n"++
                 "       soapTest --all <server-name> <port> "++
                 "<operation> <problem-file> <timeout>\n"++m
             exitWith (ExitFailure 2)

makeEndPoint :: String -> Maybe HTTPTransport
makeEndPoint uriStr = maybe Nothing 
                            (\ uri -> Just $ HTTPTransport 
                                      { httpEndpoint = uri
                                      , httpSOAPAction = Just nullURI})
                            (parseURI uriStr)

main :: IO ()
main = do
   args <- getArgs
   if length args == 6
      then if head args == "--all" 
              then allServices (tail args) 
              else doSoapCall Nothing args
      else if length args == 7 
           then doSoapCall (Just $ last args) $ init args
           else usage "too few arguments"

allServices :: [String] -> IO ()
allServices args 
    | length args == 5 = mapM_ doCall services
    | otherwise = usage "somthing went wrong with allServices"
    where doCall s = do
             putStrLn $ "soapTest: Trying Service "++show s++"..."
             doSoapCall Nothing (take 2 args ++ s: drop 2 args)
             putStrLn "----------------\n"

doSoapCall :: Maybe String -> [String] -> IO ()
doSoapCall mopts (server:port:service:operation:problemFile:timeoutStr:[]) =
    do problem <- readFile problemFile
       let (timeout :: Int) = read timeoutStr
           -- problem = "Egal"
       maybe (usage "please give a valid server name and port number")
             (\ endPoint -> do
                 (res::Either SimpleFault MathServOutput) 
                     <- soapCall endPoint $
                        mkProveProblem mopts service operation problem timeout
                 case res of
                  Left err -> putStrLn $ show err
                  Right resp -> do
                      writeFile (problemFile++".xml") $ getResponse resp
                      let xmlCont = getResponse resp
                      mtrees <- parseXML xmlCont
                      maybe (putStrLn $ "no parse of:\n"++xmlCont)
                            putXML
                            mtrees   
             )
             (makeEndPoint $ 
                "http://"++server++':':port++"/axis/services/"++service)
doSoapCall _ _ = fail $ "wrong number of arguments:\n" ++ 
              " ./soapTest <server> <port> <service> <problemFile> <timelimit>"
