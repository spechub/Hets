{- |
    a.jakubauskas@jacobs-university.de
    A wrapper/interface for MMT
-}
module MMT.Hets2mmt
    where

import System.Process
import GHC.IO.Handle
import Common.Result
import Common.Id
import Static.DevGraph
import Common.LibName

jar :: String
jar = "hets-mmt-standalone.jar"

staloneclass :: String
staloneclass = "com.simontuffs.onejar.Boot"

{-
callMMT :: String -> IO ExitCode
callMMT fileName = rawSystem "java" ["-jar", jar, fileName]
-}

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

callMMT :: FilePath -> IO [Diagnosis]
callMMT fp = do
    (out, maybeErr) <- calljar fp
    case maybeErr of
      (Just err) -> return [Diag Warning out nullRange,
                            Diag Error err nullRange]
      Nothing -> return [Diag Warning out nullRange]

mmtRes :: FilePath -> IO (Result (LibName, LibEnv))
mmtRes fname = do
          putStr $ "calling MMT on " ++ fname
          dgs <- callMMT fname
          putStr $ show dgs
          return (emptyRes dgs)

emptyRes :: [Diagnosis] -> Result (LibName, LibEnv)
emptyRes = (`Result` Just (emptyLibName "MMT", emptyLibEnv))
