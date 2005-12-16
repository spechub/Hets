{- |
Module      :  $Header$
Copyright   :  (c) C. Maeder and Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

parse Isabelle theory files
-}

module Main where

import System.Environment
import Text.ParserCombinators.Parsec
import Isabelle.IsaParse

main :: IO ()
main = getArgs >>= mapM_ process

process :: String -> IO ()
process f = do
  s <- readFile f
  putStrLn $ case parse parseTheory f s of
             Right (_, b) -> show b
             Left err -> show err
