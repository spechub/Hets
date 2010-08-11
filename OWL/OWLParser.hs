{- |
Module      :  $Header$
Copyright   :  Heng Jiang, Uni Bremen 2004-2006
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

analyse OWL files by calling the external Java parser.
-}

module Main where

import OWL.OWLAnalysis
import System.Environment (getEnv, getArgs)
import Data.List
import qualified Data.Map as Map

main :: IO ()
main = do
  args <- getArgs
  if null args then
     putStrLn "usage: OWLParser <URI>"
    else mapM_ process args

isURI :: String -> Bool
isURI str = any (flip isPrefixOf str) ["http://", "file://"]

process :: String -> IO ()
process arg = do
  pwd <- getEnv "PWD"
  let uriArg = if isURI arg then arg else "file://" ++ case arg of
        '/' : _ -> arg
        _ -> pwd ++ "/" ++ arg
  res <- parseOWL uriArg
  putStrLn $ uriArg ++ " (top-level)"
  mapM_ putStrLn $ Map.keys res
