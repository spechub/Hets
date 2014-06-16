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

import Data.List
import Data.Maybe

showFileType :: FilePath -> IO ()
showFileType fn = do
  res <- getMagicFileType (Just "--mime-type") fn
  case res of
    Right s -> putStrLn s
    Left err -> do
      hPutStrLn stderr err
      exitWith $ ExitFailure 2

getMagicFileType :: Maybe String -> FilePath -> IO (Either String String)
getMagicFileType pm fn = do
  magic <- getEnvDef "HETS_MAGIC" ""
  res <- if null magic then return $ Left "" else
      getFileType Nothing Nothing magic
  case res of
    Right s | isInfixOf "magic" s ->
        getFileType (Just magic) pm fn
    _ -> do
      putStrLn "set HETS_MAGIC to a proper magic file"
      getFileType Nothing pm fn

getFileType :: Maybe FilePath -> Maybe String -> FilePath
  -> IO (Either String String)
getFileType mmf mp fn = do
  (ex, out, err) <- executeProcess "file"
    (maybe [] (\ mf -> ["-m", mf]) mmf
    ++ maybeToList mp ++ ["-b", fn]) ""
  let unexp = fn ++ ": unexpected file type "
  return $ case (ex, lines out) of
    (ExitSuccess, ls) -> if null err then case ls of
        [l] -> Right l
        _ -> Left $ unexp ++ "output:\n" ++ out
      else Left $ unexp ++ "error:\n" ++ err
    _ -> Left $ unexp ++ "exit code: " ++ show ex
