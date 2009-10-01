{- |
Module      :  $Header$
Description :  parse a heterogeneous proof script and return it as pgip-xml
Copyright   :  (c) Christian Maeder, DFKI GmbH 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable
-}

module Main where

import PGIP.XMLstate
import PGIP.ParseProofScript (parseContent, xmlLitCmds)

import Text.XML.Light as XML

import System.Environment

parseHPF :: FilePath -> IO ()
parseHPF fp = do
  str <- readFile fp
  putStrLn $ showElement $ case parseContent fp str of
    Left err -> genErrorResponse True err
    Right rs -> genNormalResponse "" $ xmlLitCmds "" False rs

main :: IO ()
main = getArgs >>= mapM_ parseHPF
