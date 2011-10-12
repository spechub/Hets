{- |
Module      :  $Header$
Description :  test xmldiff
Copyright   :  (c) C. Maeder, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

-}

module Main (main) where

import Text.XML.Light
import Common.XmlDiff

import Control.Monad
import qualified Data.Set as Set
import qualified Data.Map as Map
import System.Environment

hetsTags :: UnordTags
hetsTags = Map.fromList
  $ map (\ (e, as) -> (unqual e, Set.fromList $ map unqual as))
  [ ("DGNode", ["name"])
  , ("DGLink", ["linkid", "source", "target"]) ]

main :: IO ()
main = do
  args <- getArgs
  case args of
    [f1, f2] -> do
      s1 <- readFile f1
      s2 <- readFile f2
      case (parseXMLDoc s1, parseXMLDoc s2) of
        (Just e1, Just e2) -> let
          ds = xmlDiff hetsTags [] Map.empty [Elem e1] [Elem e2]
          in unless (null ds) . putStrLn . ppTopElement $ mkMods ds
        _ -> error "parseXMLDoc"
    _ -> error $ "wrong arguments: " ++ show args
