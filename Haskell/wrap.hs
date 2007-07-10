{- |
Module      :  $Id$
Description :  a standalone Haskell wrapper parser
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

test the haskell wrapper
-}

module Main where

import System.Environment
import Haskell.Wrapper
import Common.Lexer
import Text.ParserCombinators.Parsec

main :: IO ()
main = getArgs >>= mapM_ process

process :: String -> IO ()
process f = do
  s <- readFile f
  case parse (hStuff << eof) f s of
             Right x -> putStrLn x
             Left err -> error $ show err
