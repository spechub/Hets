{- |
Module      :  ./Common/ProverTools.hs
Description :  Check for availability of provers
Copyright   :  (c) Dminik Luecke, and Uni Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

check for provers
-}

module Common.ProverTools where

import Common.Utils

import System.Directory
import System.FilePath

missingExecutableInPath :: String -> IO Bool
missingExecutableInPath name = do
  mp <- findExecutable name
  case mp of
    Nothing -> return True
    Just name' -> do
      p1 <- check4File (takeFileName name') "PATH" ()
      p2 <- check4File (takeFileName name') "Path" ()
      return . null $ p1 ++ p2

check4FileAux :: String -- ^ file name
              -> String -- ^ Environment Variable
              -> IO [String]
check4FileAux name env = do
      pPath <- getEnvDef env ""
      let path = "" : splitPaths pPath
      exIT <- mapM (doesFileExist . (</> name)) path
      return $ map fst $ filter snd $ zip path exIT

-- | Checks if a file exists in PATH
checkBinary :: String -> IO (Maybe String)
checkBinary name =
  fmap
    ( \l ->
        if null l
          then Just $ "missing binary in $PATH: " ++ name
          else Nothing
    )
    $ check4FileAux name "PATH"

-- | Checks if a file exists
check4File :: String -- ^ file name
           -> String -- ^ Environment Variable
           -> a
           -> IO [a]
check4File name env a = do
      ex <- check4FileAux name env
      return [a | not $ null ex ]

-- | check for java and the jar file in the directory of the variable
check4jarFile :: String -- ^ environment Variable
  -> String -- ^ jar file name
  -> IO (Bool, FilePath)
check4jarFile = check4jarFileWithDefault ""

check4jarFileWithDefault
  :: String -- ^ default path
  -> String -- ^ environment Variable
  -> String -- ^ jar file name
  -> IO (Bool, FilePath)
check4jarFileWithDefault def var jar = do
  pPath <- getEnvDef var def
  hasJar <- doesFileExist $ pPath </> jar
  return (hasJar, pPath)

-- | environment variable for HETS_OWL_TOOLS
hetsOWLenv :: String
hetsOWLenv = "HETS_OWL_TOOLS"

-- | check for the jar file under HETS_OWL_TOOLS
check4HetsOWLjar :: String -- ^ jar file name
  -> IO (Bool, FilePath)
check4HetsOWLjar = check4jarFileWithDefault "OWL2" hetsOWLenv

checkOWLjar :: String -> IO (Maybe String)
checkOWLjar name =
  fmap (\ (b, p) -> if b then Nothing else
       Just $ "missing jar ($" ++ hetsOWLenv ++ "): " ++ (p </> name))
  $ check4HetsOWLjar name
