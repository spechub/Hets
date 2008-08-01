module Main where

import System.Environment
import Common.ATerm.ReadWrite
import Common.ATerm.Unshared
import Common.ATerm.Diff

main :: IO ()
main = do args <- getArgs
          if length args == 2
             then atDiffFP (args!!0) (args!!1)
             else putStrLn "Usage: hatdiff file1 file2"

atDiffFP :: FilePath -> FilePath -> IO ()
atDiffFP fp1 fp2 =
    do at1 <- atermFromFile fp1
       at2 <- atermFromFile fp2
       let (at,diffs) = atDiff at1 at2
       if null diffs then return () else do
           putStrLn (writeATerm (toATermTable at))
           putStrLn (writeATerm (toATermTable (AList diffs [])))

atermFromFile :: FilePath -> IO ATerm
atermFromFile fp =
    do str <- readFile fp
       return (getATermFull (readATerm str))
