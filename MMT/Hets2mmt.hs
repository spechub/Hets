{- |
Module      :  ./MMT/Hets2mmt.hs
Description :  interface for MMT jar
Copyright   :
License     :
Maintainer  :  a.jakubauskas@jacobs-university.de
Stability   :  experimental
Portability :
-}
module MMT.Hets2mmt (
    mmtRes,
    callSpec
    )
    where

import System.Process
import System.IO
import Common.Result
import Common.Id
import Static.DevGraph
import Common.LibName
import Framework.Analysis (addLogic2LogicList)
import System.FilePath
import Common.Utils
-- import MMT.XMLtoPT

{- import System.IO.Unsafe
import Text.ParserCombinators.Parsec -}

jar :: String
jar = "hets-mmt-standalone.jar"

staloneclass :: String
staloneclass = "com.simontuffs.onejar.Boot"

calljar :: FilePath -> IO (String, Maybe String)
calljar fileName = do
  (_, Just hout, maybeErr, _) <- createProcess (
              proc "java" ["-cp",
                           jar,
                           staloneclass,
                           "-newLogic",
                           fileName])
              { std_out = CreatePipe }
  cont <- hGetContents hout
  case maybeErr of
    (Just hErr) -> do
            err <- hGetContents hErr
            putStr err
            return (cont, Just err)
    Nothing -> return (cont, Nothing)

callSpec :: FilePath -> IO (String, Maybe String)
callSpec fileName = do
  putStr "creating process\n"
  (_, Just hout, maybeErr, _) <- createProcess (
              proc "java" ["-cp",
                           jar,
                           staloneclass,
                           "-readSpec",
                           fileName])
              { std_out = CreatePipe }
  cont <- hGetContents hout
  -- putStr cont
  case maybeErr of
    (Just hErr) -> do
            err <- hGetContents hErr
            putStr err
            return (cont, Just err)
    Nothing -> return (cont, Nothing)

callMMT :: FilePath -> IO [Diagnosis]
callMMT fp = do
    (out, maybeErr) <- calljar fp
    case maybeErr of
      (Just err) -> return [Diag Warning out nullRange,
                            Diag Error err nullRange]
      Nothing -> return [Diag Warning out nullRange]

mmtRes :: FilePath -> IO (Result (LibName, LibEnv))
mmtRes fname = do
          libDir <- getEnvDef "HETS_LIB" ""
          putStr $ "HETS_LIB at " ++ libDir
          putStr $ "calling MMT on " ++ libDir ++ fname
          dgs <- callMMT (libDir </> fname)
          putStr $ show dgs
          addLogic2LogicList $ dropExtension fname
          return (emptyRes (dropExtension fname) dgs)

emptyRes :: String -> [Diagnosis] -> Result (LibName, LibEnv)
emptyRes lname = (`Result` Just (emptyLibName lname, emptyLibEnv))
