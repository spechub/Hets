module Main where

import OWL_DL.ReadWrite
import Common.ATerm.Lib
-- import System(getArgs)
import qualified Common.Lib.Map as Map

{-
main :: IO()
main =
    do filename <- getArgs
       if null filename then
          putStrLn "Usage: runhugs ToHaskellAS.hs <filename>"
          else do 
                  str <- readFile $ head filename  
                  let aterm = getATermFull $ readATerm str
                  case aterm of
                      AAppl "OWLParserOutput" [valid, msg, ns, onto] _ ->
                          putStrLn $ show ((fromShATerm $ toATermTable onto)::Ontology)
                      _ -> error "false file."

processor :: String -> IO()
processor filename = 
    do d <- readFile filename
       let aterm = getATermFull $ readATerm d
       case aterm of
          AAppl "OWLParserOutput" [valid, msg, ns, onto] _ ->
             putStrLn $ show ((fromShATerm $ toATermTable onto)::Ontology)
          _ -> error "false file."

-}

processor2 :: String -> IO()
processor2 filename = 
    do d <- readFile filename
       let aterm = getATermFull $ readATerm d
       case aterm of
          AAppl "OWLParserOutput" [valid, msg, ns, onto] _ ->
              do
                  putStrLn $ fromATerm valid
                  putStrLn $ show (buildMsg msg)
                  putStrLn $ show (buildNS ns)
                  putStrLn $ show ((fromShATerm $ toATermTable onto)::Ontology)
          _ -> error "false file."

    where buildNS :: ATerm -> Namespace
          buildNS at = case at of
                       AAppl "Namespace" [AList nsl _] _ ->
                           mkMap nsl (Map.empty)
                       _ -> error ""
          
          mkMap :: [ATerm] -> Namespace -> Namespace
          mkMap [] mp = mp 
          mkMap (h:r) mp = case h of
                           AAppl "NS" [name, uri] _ ->
                               mkMap r (Map.insert (fromATerm name) (fromATerm uri) mp)
                           _ -> error "illegal namespace."

          buildMsg :: ATerm -> Message
          buildMsg at = case at of
                        AAppl "Message" [AList msgl _] _ ->
                                mkMsg msgl (Message [])
                        _ -> error "illegal message:)"

          mkMsg :: [ATerm] -> Message -> Message
          mkMsg [] (Message msg) = Message (reverse msg)
          mkMsg (h:r) (Message preRes) =
                case h of
                        AAppl "Message" [a,b,c] _ ->
                            mkMsg r (Message ((fromATerm a, fromATerm b, fromATerm c):preRes))
                        AAppl "ParseWarning" warnings _ ->
                            mkMsg r (Message (("ParserWarning", fromATerm $ head warnings, ""):preRes))
                        AAppl "ParseError" errors _ ->
                            mkMsg r (Message (("ParserError", fromATerm $ head errors, ""):preRes))
                        _ -> error "unknow message."


