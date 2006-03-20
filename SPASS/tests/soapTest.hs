
-- | simple test program that sends a file as soap message to a 
-- MathServ Broker

module Main where

import System.Environment (getArgs)
import System.IO
import System.Exit

import Network.URI
import Network.Service

import Text.XML.Serializer
import Org.Xmlsoap.Schemas.Soap.Envelope as ENV

import Data.Generics2
import Data.Typeable

data MathServServices = 
    ProveProblemOpt { in0 :: String
                    , in1 :: Int}

$(xmlify [''MathServServices] [])

instance XMLNamespace MathServServices

mkProveProblem :: String -> Int -> MathServServices
mkProveProblem = ProveProblemOpt

usage :: String -> IO ()
usage m = do hPutStrLn stderr $
                 "Usage: soapTest <server-name> <port> <service-name> "++
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
   if length args == 5 
      then doSoapCall args
      else usage "too few arguments"

doSoapCall :: [String] -> IO ()
doSoapCall (server:port:service:problemFile:timeoutStr:[]) =
    do problem <- readFile problemFile
       let (timeout :: Int) = read timeoutStr
           -- problem = "Egal"
       maybe (usage "please give a valid server name and port number")
             (\ endPoint -> do
                 (res::Either Fault String) <- soapCall endPoint $
                                           mkProveProblem problem timeout
                 case res of
                  Left f -> do putStrLn "SOAP Fault"
                               putStrLn $ show f
                  Right r -> do putStrLn "Got a result"
                                putStrLn $ show r
             )
             (makeEndPoint $ 
                "http://"++server++':':port++"/axis/services/Broker")
doSoapCall _ = fail "wrong number of arguments"