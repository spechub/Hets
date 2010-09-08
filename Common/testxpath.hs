{- |
Module      :  $Header$
Description :  standalone parser for path expressions
Copyright   :  (c) C. Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

standalone parser for path expressions
-}

module Main (main) where

import Common.XPath
import Text.ParserCombinators.Parsec
import Common.Parsec

main :: IO ()
main = do
  str <- getContents
  mapM_ process $ zip [1 ..] $ lines str

process :: (Int, String) -> IO ()
process (n, str) = case parse (spaces >> expr << eof) "" str of
  Left err -> fail $ "line " ++ show n ++ ": " ++ show err
  Right e -> print e
