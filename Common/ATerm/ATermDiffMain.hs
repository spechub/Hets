{- |
Module      :  $Header$
Copyright   :  (c) C. Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

-}

module Main (main) where

import System.Environment
import ATerm.ReadWrite
import ATerm.Unshared
import ATerm.Diff
import Control.Monad

main :: IO ()
main = do
  args <- getArgs
  case args of
    [x, y] -> atDiffFP x y
    _ -> putStrLn "expected two argument filenames"

atDiffFP :: FilePath -> FilePath -> IO ()
atDiffFP fp1 fp2 =
    do at1 <- atermFromFile fp1
       at2 <- atermFromFile fp2
       let (at, diffs) = atDiff at1 at2
       unless (null diffs) $ do
           putStrLn (writeATerm (toATermTable at))
           putStrLn (writeATerm (toATermTable (AList diffs [])))

atermFromFile :: FilePath -> IO ATerm
atermFromFile fp =
    do str <- readFile fp
       return (getATermFull (readATerm str))
