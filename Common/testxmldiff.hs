{- |
Module      :  ./Common/testxmldiff.hs
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
import System.Environment

main :: IO ()
main = do
  args <- getArgs
  case args of
    [f1, f2] -> do
      s1 <- readFile f1
      s2 <- readFile f2
      case (parseXMLDoc s1, parseXMLDoc s2) of
        (Just e1, Just e2) -> let
          ds = hetsXmlChanges e1 e2
          in unless (null ds) . putStrLn . ppTopElement $ mkMods ds
        _ -> error "parseXMLDoc"
    _ -> error $ "wrong arguments: " ++ show args
