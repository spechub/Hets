{- |
Module      :  $Header$
Description :  Check for availability of provers
Copyright   :  (c) Dminik Luecke, and Uni Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

check for provers
-}

module Common.ProverTools where

import Common.Utils

import System.Directory
import System.IO.Unsafe
import System.FilePath

-- | Checks if a Prover Binary exists and is executable
-- in an unsafe manner
unsafeProverCheck :: String -- ^ prover Name
                  -> String -- ^ Environment Variable
                  -> a
                  -> [a]
unsafeProverCheck name env = unsafePerformIO . check4Prover name env

-- | Checks if a Prover Binary exists and is executable
check4Prover :: String -- ^ prover Name
             -> String -- ^ Environment Variable
             -> a
             -> IO [a]
check4Prover name env a = do
      ex <- check4FileAux name env
      case ex of
        [] -> return []
        _ -> do
          execI <- mapM (getPermissions . (</> name)) ex
          return [ a | any executable execI ]

missingExecutableInPath :: String -> IO Bool
missingExecutableInPath name = do
  mp <- findExecutable name
  case mp of
    Nothing -> return True
    Just _ -> fmap null $ check4Prover name "PATH" ()

-- | Checks if a file exists in an unsafe manner
unsafeFileCheck :: String -- ^ prover Name
                -> String -- ^ Environment Variable
                -> a
                -> [a]
unsafeFileCheck name env = unsafePerformIO . check4File name env

check4FileAux :: String -- ^ file name
              -> String -- ^ Environment Variable
              -> IO [String]
check4FileAux name env = do
      pPath <- getEnvDef env ""
      let path = "" : splitOn ':' pPath
      exIT <- mapM (doesFileExist . (</> name)) path
      return $ map fst $ filter snd $ zip path exIT

-- | Checks if a file exists
check4File :: String -- ^ file name
           -> String -- ^ Environment Variable
           -> a
           -> IO [a]
check4File name env a = do
      ex <- check4FileAux name env
      return [a | not $ null ex ]
