{- |
Module      :  ./Common/FileType.hs
Description :  checking the file type
Copyright   :  (c) C. Maeder, DFKI 2014
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

check the file content by using the unix tool file
-}

module Common.FileType (getMagicFileType, getChecksum) where

import System.Exit

import Common.Utils
import Common.Result
import Common.ResultT

import Data.List
import Data.Maybe

getChecksum :: FilePath -> ResultT IO String
getChecksum fn = ResultT $ do
  ckprg <- getEnvDef "HETS_CHECKSUM" "shasum -a 256"
  case words ckprg of  -- no support for options with spaces
    [] -> return $ fail "set HETS_CHECKSUM to a proper command"
    cmd : args -> do
      (ex, out, err) <- executeProcess cmd (args ++ [fn]) ""
      return $ case (ex, map words $ lines out) of
        (ExitSuccess, (h : _) : _) | null err ->
          justHint h $ h ++ "  " ++ fn
        _ -> fail $ "could not determine checksum: "
          ++ shows ex "\n" ++ out
          ++ if null err then "" else "\nerror\n" ++ err

getMagicFileType :: Maybe String -> FilePath -> ResultT IO String
getMagicFileType mp fn = ResultT $ do
  res <- runResultT $ getFileType Nothing (Just "--mime-encoding") fn
  runResultT $ case maybeResult res of
    Just s -> do
      liftR $ justHint () $ "mime-encoding: " ++ s
      if any (`isInfixOf` s) ["binary", "unknown"]
        then do
          liftR $ justWarn () $ "no support for " ++ s ++ " file: " ++ fn
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
  (ex, out, err) <- executeProcessWithEnvironment "file"
    (maybeToList mp ++ ["--brief", fn]) ""
    $ maybe [] (\ mf -> [("MAGIC", mf)]) mmf
  let unexp = "unexpected file type "
  return $ case (ex, lines out) of
    (ExitSuccess, ls) -> if null err then case ls of
        [l] -> return l
        _ -> fail $ unexp ++ "output:\n" ++ out
      else fail $ unexp ++ "error:\n" ++ err
    _ -> fail $ unexp ++ "exit code: " ++ show ex
