{- |
Module      :  $Header$
Description :  checking the file type
Copyright   :  (c) C. Maeder, DFKI 2014
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

check the file content by using the unix tool file
-}

module Common.FileType (showFileType) where

import System.Exit
import System.IO

import Common.Utils

showFileType :: FilePath -> IO ()
showFileType fn = do
  (ex, out, err) <- executeProcess "file" ["-b", "--mime-type", fn] ""
  case (ex, lines out) of
    (ExitSuccess, [l]) | null err -> putStrLn l
    _ -> do
      hPutStrLn stderr $ "hets unexpected file type output for: " ++ fn
      hPutStrLn stderr err
      exitWith ex
