{- |
Module      :  $Header$
Copyright   :  (c) Dominik Luecke, 2008
License     :  GPLv2 or higher

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable

This module implements conservativity checks for OWL 2.0 based on the
the syntactic locality checker written in Java from the OWL-Api.
-}

module OWL.Conservativity
  ( localityJar
  , conserCheck
  ) where

import Common.AS_Annotation
import Common.Consistency
import Common.Result
import Common.ProverTools
import Common.Utils

import GUI.Utils ()

import OWL.AS
import OWL.Morphism
import OWL.Print (printOWLBasicTheory)
import OWL.Sign

import System.Directory
import System.Exit
import System.IO

localityJar :: String
localityJar = "OWLLocality.jar"

-- | Conservativity Check for Propositional Logic
conserCheck :: String                        -- ^ Conser type
           -> (Sign, [Named Axiom])       -- ^ Initial sign and formulas
           -> OWLMorphism                    -- ^ morphism between specs
           -> [Named Axiom]               -- ^ Formulas of extended spec
           -> IO (Result (Maybe (Conservativity, [Axiom])))
conserCheck ct = uncurry $ doConservCheck localityJar ct

-- | Real conservativity check in IO Monad
doConservCheck :: String            -- ^ Jar name
               -> String            -- ^ Conser Type
               -> Sign              -- ^ Signature of Onto 1
               -> [Named Axiom]  -- ^ Formulas of Onto 1
               -> OWLMorphism       -- ^ Morphism
               -> [Named Axiom]  -- ^ Formulas of Onto 2
               -> IO (Result (Maybe (Conservativity, [Axiom])))
doConservCheck jar ct sig1 sen1 mor sen2 =
  let ontoFile = printOWLBasicTheory (otarget mor, filter isAxiom sen2)
      sigFile = printOWLBasicTheory (sig1, filter isAxiom sen1)
  in runLocalityChecker jar ct (show ontoFile) (show sigFile)

-- | Invoke the Java checker
runLocalityChecker :: String            -- ^ Jar name
                   -> String            -- ^ Conser Type
                   -> String            -- ^ Ontology
                   -> String            -- ^ String
                   -> IO (Result (Maybe (Conservativity, [Axiom])))
runLocalityChecker jar ct onto sig = do
  (progTh, toolPath) <- check4HetsOWLjar jar
  if progTh then withinDirectory toolPath $ do
      tempDir <- getTemporaryDirectory
      sigFile <- writeTempFile sig tempDir "ConservativityCheck.sig.owl"
      let tLimit = 800
          ontoFile = sigFile ++ ".onto.owl"
          command = "java -jar " ++ jar ++ " file://" ++ ontoFile
                     ++ " file://" ++ sigFile ++ " " ++ ct
      writeFile ontoFile onto
      (mExit, outh, _) <- timeoutCommand tLimit command
      removeFile ontoFile
      removeFile sigFile
      case mExit of
        Just cont -> parseOutput outh cont
        Nothing ->
          return $ fail $ "Timelimit " ++ show tLimit ++ " exceeded"
    else return $ fail $ jar ++ " not found"

parseOutput :: Handle -- ^ handel of stdout
            -> ExitCode
            -> IO (Result (Maybe (Conservativity, [Axiom])))
parseOutput outh exit = do
  ls1 <- hGetContents outh
  let ls = lines ls1
  return $ case exit of
    ExitFailure 10 -> return $ Just (Cons, [])
    ExitFailure 20 -> fail $ unlines ls
    x -> fail $ "Internal program error: " ++ show x ++ "\n" ++ unlines ls
