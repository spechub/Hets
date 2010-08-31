{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}
{- Module which tests parsing an MMiSS document file (given as input),
   verifying it, structuring it, converting it to CodedValue and converting it
   back again. -}

import System
import System.IO

import Taxonomy.OntoParser
import Taxonomy.MMiSSOntology
import Taxonomy.MMiSSOntologyGraph
import Data.Graph.Inductive.Graphviz

import GUI.HTkUtils

useMsg :: IO ()
useMsg = do
  putStrLn "Tool for checking and converting MMiSS ontologies"
  putStrLn "usage:"
  putStrLn "  ontotool [OPTIONS] [STARTNODENAME] INPUTFILE"
  putStrLn "Options are:"
  putStrLn " -owl     : print out OWL representation"
  putStrLn " -daVinci : start daVinci and show ontology as graph"

main :: IO ()
main =
   do args <- System.getArgs
      if elem "--help" args then do
        useMsg
        exitWith ExitSuccess
        else done
      fileName <- if null args then do
        useMsg
        exitWith (ExitFailure 1)
        else return (last args)
      let startNodeName = case reverse args of
            _ : sd : _ -> Just sd
            _ -> Nothing
      weOntology <- parseMMiSSOntologyFile fileName
      onto <- weither (\ message ->
         let str = "The following errors occured during parsing:\n"
         in error (str ++ message)) (\ o -> let messages = isComplete o in
                 if null messages then do
                   hPutStr stderr
                     "Parsing and checking ontology: successful\n"
                   return o
                 else do
                   hPutStr stderr (unlines messages)
                   return o) weOntology
      if elem "-owl" args then do
            putStr $ exportOWL onto
            done
        else if elem "-dot" args then do
            putStr $ graphviz' $ getClassGraph onto
            done
        else done
      if elem "-daVinci" args then do
            displayClassGraph onto startNodeName
            getLine
            done
        else done
