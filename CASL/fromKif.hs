{- |
Module      :  $Header$
Copyright   :  (c) C.Maeder, Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable

convert .kif to .casl
-}
module Main where

import CASL.Kif
import CASL.Kif2CASL
import CASL.Print_AS_Basic()

import Common.Utils
import Common.DocUtils

import Text.ParserCombinators.Parsec
import System.Environment

main :: IO ()
main = getArgs >>= mapM_ process

process :: String -> IO ()
process s = do
  e <- parseFromFile kifProg s
  case e of
    Left err -> putStrLn $ show err
    Right l -> do
        let f = fst (stripSuffix [".kif"] s) ++ ".casl"
        writeFile f $ showDoc (kif2CASL l) "\n"
