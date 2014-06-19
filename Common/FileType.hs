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

module Common.FileType (getMagicFileType) where

import System.Exit

import Common.Utils
import Common.Result
import Common.ResultT

import Data.List
import Data.Maybe

getMagicFileType :: Maybe String -> FilePath -> ResultT IO String
getMagicFileType mp fn = ResultT $ do
  res <- runResultT $ getFileType Nothing (Just "--mime-encoding") fn
  runResultT $ case maybeResult res of
    Just s -> if isInfixOf "binary" s
      then do
        liftR $ justWarn () $ "no support for binary file: " ++ fn
        getFileType Nothing mp fn
      else getMagicFileTypeAux mp fn
    _ -> liftR res

getMagicFileTypeAux :: Maybe String -> FilePath -> ResultT IO String
getMagicFileTypeAux pm fn = ResultT $ do
  magic <- getEnvDef "HETS_MAGIC" ""
  res <- if null magic then return $ fail "null magic" else
      runResultT $ getFileType Nothing Nothing magic
  runResultT $ case maybeResult res of
    Just s | isInfixOf "magic" s -> getFileType (Just magic) pm fn
    _ -> do
      liftR $ justWarn () "set HETS_MAGIC to a proper magic file"
      getFileType Nothing pm fn

getFileType :: Maybe FilePath -> Maybe String -> FilePath -> ResultT IO String
getFileType mmf mp fn = ResultT $ do
  (ex, out, err) <- executeProcess "file"
    (maybe [] (\ mf -> ["-m", mf]) mmf
    ++ maybeToList mp ++ ["-b", fn]) ""
  let unexp = "unexpected file type "
  return $ case (ex, lines out) of
    (ExitSuccess, ls) -> if null err then case ls of
        [l] -> return l
        _ -> fail $ unexp ++ "output:\n" ++ out
      else fail $ unexp ++ "error:\n" ++ err
    _ -> fail $ unexp ++ "exit code: " ++ show ex
