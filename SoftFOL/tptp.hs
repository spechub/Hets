{- |
Module      :  $Id$
Description :  a standalone tptp parser
Copyright   :  (c) C.Maeder, DFKI Lab Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

parse tptp v3.4.0.1 files
-}

module Main where

import System.Environment
import Text.ParserCombinators.Parsec
import SoftFOL.ParseTPTP

main :: IO ()
main = getArgs >>= mapM_ process

process :: String -> IO ()
process f = do
  s <- readFile f
  case parse tptp f s of
    Right b -> writeFile (f ++ ".tptp") $ shows (prTPTPs b) "\n"
    Left err -> print err
