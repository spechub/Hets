{- |
Module for testing Static.FromXml manually on command line level
-}

module Main where

import Static.FromXml
import Static.DevGraph (emptyDG)
import Comorphisms.LogicGraph (logicGraph)
import Text.XML.Light (parseXMLDoc)


main :: IO()
main = do
  putStrLn "please enter filepath of xml file to read"
  path <- getLine
  xml <- readFile path
  case parseXMLDoc xml of
    Just el -> do
      let dg = fromXml logicGraph emptyDG el
      putStrLn $ "Success! Result graph is:\n" ++ show dg
    Nothing -> do putStrLn "Failed to parse xml element!"

