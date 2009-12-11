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

module OWL.Conservativity (conserCheck) where

import Common.AS_Annotation
import Common.Consistency
import Common.Result
import Common.Utils

import Data.Time.Clock (UTCTime(..), getCurrentTime)
import Data.Maybe (isJust, fromJust)

import GUI.Utils ()

import OWL.AS
import OWL.Morphism
import OWL.Print (printOWLBasicTheory)
import OWL.Sign

import System.Directory
import System.Exit
import System.IO
import System.IO.Unsafe

toolName :: String
toolName = "owl_locality"

-- | Conservativity Check for Propositional Logic
conserCheck :: String                        -- ^ Conser type
           -> (Sign, [Named Axiom])       -- ^ Initial sign and formulas
           -> OWLMorphism                    -- ^ morphism between specs
           -> [Named Axiom]               -- ^ Formulas of extended spec
           -> Result (Maybe (Conservativity, [Axiom]))
conserCheck ct (sig, forms) mor =
  unsafePerformIO . doConservCheck "OWLLocality.jar" ct sig forms mor

-- | Real conservativity check in IO Monad
doConservCheck :: String            -- ^ Jar name
               -> String            -- ^ Conser Type
               -> Sign              -- ^ Signature of Onto 1
               -> [Named Axiom]  -- ^ Formulas of Onto 1
               -> OWLMorphism       -- ^ Morphism
               -> [Named Axiom]  -- ^ Formulas of Onto 2
               -> IO (Result (Maybe (Conservativity, [Axiom])))
doConservCheck jar ct sig1 sen1 mor sen2 = do
  let ontoFile = printOWLBasicTheory (otarget mor, filter isAxiom sen2)
      sigFile  = printOWLBasicTheory (sig1, filter isAxiom sen1)
  runLocalityChecker jar ct (show ontoFile) (show sigFile)

getEnvSec :: String -> IO String
getEnvSec s = getEnvDef s ""

check4Tool :: String -> IO (Bool, Bool)
check4Tool jar = do
  pPath <- getEnvSec "HETS_OWL_TOOLS"
  progTh <- doesFileExist $ pPath ++ "/" ++ jar
  progEx <- if progTh then do
      progPerms <- getPermissions $ pPath ++ "/" ++ toolName
      return $ executable progPerms
    else return False
  return (progTh, progEx)

-- | Invoke the Java checker
runLocalityChecker :: String            -- ^ Jar name
                   -> String            -- ^ Conser Type
                   -> String            -- ^ Ontology
                   -> String            -- ^ String
                   -> IO (Result (Maybe (Conservativity, [Axiom])))
runLocalityChecker jar ct onto sig = do
  let tLimit = 800
  (progTh, _) <- check4Tool jar
  if progTh then do
      t <- getCurrentTime
      tempDir <- getTemporaryDirectory
      toolPath <- getEnvSec "HETS_OWL_TOOLS"
      let baseName = "ConservativityCheck"
          fileName = tempDir ++ "/" ++ baseName ++ show (utctDay t)
                     ++ "-" ++ show (utctDayTime t)
          ontoFile = fileName ++ ".onto.owl"
          sigFile  = fileName ++ ".sig.owl"
          command  = "java -jar " ++ jar ++ " file://" ++ ontoFile
                     ++ " file://" ++ sigFile ++ " " ++ ct
      writeFile ontoFile onto
      writeFile sigFile sig
      setCurrentDirectory toolPath
      (mExit, outh, _) <- timeoutCommand tLimit command
      (result, _) <- if isJust mExit then parseOutput outh $ fromJust mExit
        else return (fail $ "Timelimit " ++ show tLimit ++ " exceeded", [""])
      removeFile ontoFile
      removeFile sigFile
      return result
    else return $ fail $ toolName ++ " not found"

parseOutput :: Handle -- ^ handel of stdout
            -> ExitCode
            -> IO ((Result (Maybe (Conservativity, [Axiom]))), [String])
parseOutput outh exit = do
  ls1 <- hGetContents outh
  let ls = lines ls1
  case exit of
    ExitFailure 10 -> return (return $ Just (Cons, []), ls)
    ExitFailure 20 -> return (fail $ unlines ls, ls)
    x -> return (fail $ "Internal program error: " ++ show x ++ "\n"
                        ++ unlines ls, ls)
