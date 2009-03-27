{-# OPTIONS_GHC -fth -w #-}
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
import Text.Regex

import Text.XML.Serializer
import Org.Xmlsoap.Schemas.Soap.Envelope as ENV

import Data.Generics2
import Data.Typeable
import Data.List (intercalate)

import Control.Monad (mapM_,when)

data MathServServices =
    ProveProblemOpt { in0 :: String
                    , in1 :: Int}
  | ProveProblemChoice { in0 :: String
                       , in1 :: Int}
  | Shutdown
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
  | ShutdownResponse
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
    ShutdownResponse -> "\"no response message expected\"\n"

mkProveProblem :: Maybe String -- ^ extra options
               -> String -- ^ Service name
               -> String -- ^ SOAP operation name
               -> String -> Int -> MathServServices
mkProveProblem mopts service operation =
    case service of
     "Broker" -> case operation of
                 "ProveProblemOpt" -> ProveProblemOpt
                 "ProveProblemChoice" -> ProveProblemChoice
                 "Shutdown" -> \ _ _ -> Shutdown
                 _ -> fail $ "unknown Operation for service Broker\n"++
                       "known operations: ProveProblemOpt, ProveProblemChoice"
     x
         | x `elem` services -> singleATP
         | otherwise -> fail $ "unknown Service\nknown services: "
                          ++ "\"Broker\", "
                          ++ intercalate ", " (map show services)
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
                 "<problem-file> <timeout>\n"++m
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
   case args of
    _ | length args == 5 -> if head args == "--all"
                               then allServices (tail args)
                               else usage "too few arguments"
      | length args == 6 -> doSoapCall False Nothing args
      | length args == 7 -> doSoapCall False (Just $ last args) $ init args
      | otherwise -> usage "too few arguments"

allServices :: [String] -> IO ()
allServices args
    | length args == 4 =
        do putStrLn $ "soapTest: Trying Broker..."
           doSoapCall True Nothing
                      (take 2 args ++ "Broker":"ProveProblemOpt":drop 2 args)
           mapM_ doCall services

    | otherwise = usage "somthing went wrong with allServices"
    where doCall s = do
             putStrLn $ "soapTest: Trying Service "++show s++"..."
             doSoapCall True Nothing (take 2 args ++ s:"ProveTPTPProblem":
                                 drop 2 args)
             putStrLn "----------------\n"

statusRegex :: Regex
statusRegex = mkRegexWithOpts
              "\"http://www\\.mathweb\\.org/owl/status\\.owl#([^\"]*)\" ?/>"
              False False

cputimeRegex :: Regex
cputimeRegex = mkRegexWithOpts
              "<mw:cpuTime[^>]+>([0-9]+)</"
              False False

walltimeRegex :: Regex
walltimeRegex = mkRegexWithOpts
              "<mw:wallClockTime[^>]+>([0-9]+)</"
              False False

systemRegex :: Regex
systemRegex = mkRegexWithOpts
              "<mw:system>([^<>]+)</"
              False False

doSoapCall :: Bool -- ^ True means grep for status
           -> Maybe String -> [String] -> IO ()
doSoapCall grepForStatus mopts
           (server:port:service:operation:problemFile:timeoutStr:[]) =
    do problem <- readFile problemFile
       let (timeout :: Int) = read timeoutStr
           -- problem = "Egal"
       maybe (usage "please give a valid server name and port number")
             (\ endPoint -> do
                 (res::Either SimpleFault MathServOutput)
                     <- soapCall endPoint $
                        mkProveProblem mopts service operation problem timeout
                 case res of
                  Left errorMes -> putStrLn $ show errorMes
                  Right resp -> do
                      writeFile (problemFile++".xml") $ getResponse resp
                      let xmlCont = getResponse resp
                      mtrees <- parseXML xmlCont
                      let xmlStatus = maybe ("no parse")
                                            (const "valid xml")
                                            mtrees
                      when grepForStatus ( do
                           putStrLn ("Status: " ++
                                     evalRegexResult
                                          (matchRegex statusRegex xmlCont))
                           putStrLn ("Used Time: CPU: " ++
                                     evalRegexResult
                                          (matchRegex cputimeRegex xmlCont) ++
                                     "; WallClock: " ++
                                     evalRegexResult
                                          (matchRegex walltimeRegex xmlCont))
                           when (service=="Broker")
                                (putStrLn ("Used ATP system: "++
                                           evalRegexResult
                                           (matchRegex systemRegex xmlCont)))
                                         )
                      putStrLn $ "XMLStatus: "++xmlStatus
                      putStrLn xmlCont
             )
             (makeEndPoint $
                "http://"++server++':':port++"/axis/services/"++service)
    where evalRegexResult = maybe ">>not found"
                            (\ sl -> if null sl
                                     then ">>>not found"
                                     else head sl)

doSoapCall _ _ _ = fail $ "wrong number of arguments:\n" ++
              " ./soapTest <server> <port> <service> <problemFile> <timelimit>"
