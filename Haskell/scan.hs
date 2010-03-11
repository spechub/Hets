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
import System.Environment
import Haskell.Scanner
import Text.ParserCombinators.Parsec

main :: IO ()
main = getArgs >>= mapM_ process

process :: String -> IO ()
process f = do
  s <- readFile f
  case parse scan f s of
             Right x -> let o = showScan x in unless (null o) $ putStrLn o
             Left err -> fail $ show err
