{- |
Module      :  $Id$
Description :  a standalone dfg parser
Copyright   :  (c) C. Maeder and Uni Bremen 2007
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

parse dfg files
-}

module Main where

import System.Environment
import Text.ParserCombinators.Parsec
import SoftFOL.DFGParser
import SoftFOL.Print ()
import Common.DocUtils

main :: IO ()
main = getArgs >>= mapM_ process

process :: String -> IO ()
process f = do
  s <- readFile f
  case parse parseSPASS f s of
    Right b -> writeFile (f ++ ".dfg") $ shows (pretty b) "\n"
    Left err -> print err
