{- |
Module      :  $Id$
Description :  a standalone Haskell scanner
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

test the haskell scanner
-}

import Control.Monad
import Data.List
import System.Environment
import Haskell.Scanner
import Text.ParserCombinators.Parsec

main :: IO ()
main = do
  args <- getArgs
  let (opts, files) = span (isPrefixOf "-") args
  mapM_ (process $ null opts) files

process :: Bool -> String -> IO ()
process b f = do
  s <- readFile f
  case parse scan f s of
             Right x -> if b then
               let o = showScan x in unless (null o) $ putStrLn o
               else writeFile f $ processScan x
             Left err -> fail $ show err
