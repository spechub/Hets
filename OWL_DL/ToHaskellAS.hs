module Main where

import OWL_DL.ReadWrite
import Common.ATerm.Lib
import System(getArgs)

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
