{- |
Module      :  $Header$
Copyright   :  (c) Dominik Luecke, 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable

This module implements conservativity checks for OWL 2.0 based on the
the syntactic locality checker written in Java from the OWL-Api.
-}

module OWL.Conservativity
    (
     conserCheck
    )
    where

import Common.AS_Annotation
import OWL.Sign
import OWL.Morphism
import Common.Result
import Common.Consistency
import System.IO.Unsafe
import OWL.Print(printOWLBasicTheory)
import Common.DefaultMorphism

import Common.Utils
import System.Exit
import System.IO
import System.Process
import System.Directory

import Control.Concurrent
import Control.Concurrent.MVar

import Data.Time.Clock (UTCTime(..), getCurrentTime)

import GUI.Utils ()

toolName :: String
toolName = "owl_locality"

-- | Conservativity Check for Propositional Logic
conserCheck :: (Sign, [Named Sentence])      -- ^ Initial sign and formulas
           -> OWL_Morphism                   -- ^ morhpism between specs
           -> [Named Sentence]               -- ^ Formulas of extended spec
           -> Result (Maybe (ConsistencyStatus, [Sentence]))
conserCheck (sig, forms) mor nForms = unsafePerformIO $
                                      doConservCheck sig forms mor nForms

-- | Real conservativity check in IO Monad
doConservCheck :: Sign              -- ^ Signature of Onto 1
               -> [Named Sentence]  -- ^ Formulas of Onto 1
               -> OWL_Morphism      -- ^ Morhpism
               -> [Named Sentence]  -- ^ Formulas of Onto 2
               -> IO (Result (Maybe (ConsistencyStatus, [Sentence])))
doConservCheck sig1 _ mor sen2 =
    case (isInclusionDefaultMorphism mor) of
      False -> return $ fail "Morphism is not an inclusion"
      True  ->
          do
            let ontoFile = printOWLBasicTheory
                 (codOfDefaultMorphism mor, filter isAxiom sen2)
                sigFile  = printOWLBasicTheory (sig1, [])
            runLocalityChecker (show ontoFile) (show sigFile)

getEnvSec :: String -> IO String
getEnvSec s = getEnvDef s ""

check4Tool :: IO (Bool, Bool)
check4Tool =
    do
      pPath     <- getEnvSec "HETS_OWL_TOOLS"
      progTh    <- doesFileExist $ pPath ++ "/" ++ "OWLLocality.jar"
      progEx <- if (progTh)
                 then
                     do
                       progPerms <- getPermissions $ pPath ++ "/" ++ toolName
                       return $ executable $ progPerms
                 else
                     return False
      return $ (progTh, progEx)

-- | Invoke the Java checker
runLocalityChecker :: String            -- ^ Ontology
                   -> String            -- ^ String
                   -> IO (Result (Maybe (ConsistencyStatus, [Sentence])))
runLocalityChecker onto sig =
  do
    let timeLimit = 800
    (progTh, _) <- check4Tool
    case progTh of
      False ->
          do
            return $ fail (toolName ++ " not found")
      True ->
          do
            t <- getCurrentTime
            tempDir <- getTemporaryDirectory
            toolPath <- getEnvSec "HETS_OWL_TOOLS"
            let baseName = "ConservativityCheck"
            let ontoFile = tempDir ++ "/" ++ baseName ++ (show $ utctDay t) ++
                          "-" ++ (show $ utctDayTime t) ++ ".onto.owl"
                sigFile  = tempDir ++ "/" ++ baseName ++ (show $ utctDay t)
                           ++ "-" ++ (show $ utctDayTime t) ++ ".sig.owl"
            let command = "java -jar OWLLocality.jar file://" ++ ontoFile ++ " file://" ++ sigFile
            writeFile ontoFile onto
            writeFile sigFile sig
            (result, _) <-
                timeWatch timeLimit
                (
                 do
                   setCurrentDirectory(toolPath)
                   (_, outh, errh, proch) <- runInteractiveCommand command
                   res <- parseOutput outh errh proch
                   return res
                )
            removeFile ontoFile
            removeFile sigFile
            return result

parseOutput :: Handle        -- ^ handel of stdout
            -> Handle        -- ^ handel of stderr
            -> ProcessHandle -- ^ handel of process
            -> IO ((Result (Maybe (ConsistencyStatus, [Sentence]))), [String])
parseOutput outh _ proc =
    collectLines
    where
      collectLines =
          do
            procState <- waitForProcess proc
            ls1 <- hGetContents outh
            let ls = lines ls1
            case procState of
              ExitFailure 10 ->
                  do
                    return $ (return $ Just (Conservative,[]), ls)
              ExitFailure 20 ->
                  do
                    return $ (fail $ unlines ls, ls)
              x                     ->
                  do
                    return $ (fail ("Internal program error: " ++
                                    show x ++ "\n" ++ unlines ls), ls)

timeWatch :: Int -> IO ((Result (Maybe (ConsistencyStatus, [Sentence]))), [String])
           -> IO ((Result (Maybe (ConsistencyStatus, [Sentence]))), [String])
timeWatch time process =
        do
          mvar <- newEmptyMVar
          tid1 <- forkIO $ do z <- process
                              putMVar mvar (Just z)
          tid2 <- forkIO $ do threadDelay (time * 1000000)
                              putMVar mvar Nothing
          res <- takeMVar mvar
          case res of
            Just z -> do
                     killThread tid2 `catch` (\e -> putStrLn (show e))
                     return z
            Nothing -> do
                     killThread tid1 `catch` (\e -> putStrLn (show e))
                     return $ (fail $ "Timelimit " ++ show time ++ " exceeded", [""])
