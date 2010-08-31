{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}
import System.Environment
import ATerm.ReadWrite
import ATerm.Unshared
import ATerm.Diff

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
