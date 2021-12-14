{- |
Module      :  ./OWL2/Conservativity.hs
Copyright   :  (c) Dominik Luecke, 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable

This module implements conservativity checks for OWL 2.0 based on the
the syntactic locality checker written in Java from the OWL-Api.
-}

module OWL2.Conservativity
  ( localityJar
  , conserCheck
  ) where

import Common.AS_Annotation
import Common.Consistency
import Common.Result
import Common.ProverTools
import Common.Utils

import GUI.Utils ()

import OWL2.AS
import OWL2.Morphism
import OWL2.Sign
import OWL2.XMLConversion

import System.Directory
import System.Exit

localityJar :: String
localityJar = "OWLLocality.jar"

-- | Conservativity Check for Propositional Logic
conserCheck :: String                        -- ^ Conser type
           -> (Sign, [Named Axiom])       -- ^ Initial sign and formulas
           -> OWLMorphism                    -- ^ morphism between specs
           -> [Named Axiom]               -- ^ Formulas of extended spec
           -> IO (Result (Conservativity, [Axiom]))
conserCheck ct = uncurry $ doConservCheck localityJar ct

-- | Real conservativity check in IO Monad
doConservCheck :: String            -- ^ Jar name
               -> String            -- ^ Conser Type
               -> Sign              -- ^ Signature of Onto 1
               -> [Named Axiom]  -- ^ Formulas of Onto 1
               -> OWLMorphism       -- ^ Morphism
               -> [Named Axiom]  -- ^ Formulas of Onto 2
               -> IO (Result (Conservativity, [Axiom]))
doConservCheck jar ct sig1 sen1 mor sen2 =
  let ontoFile = mkODoc (otarget mor) sen2
      sigFile = mkODoc sig1 (filter isAxiom sen1)
  in runLocalityChecker jar ct ontoFile sigFile

-- | Invoke the Java checker
runLocalityChecker :: String            -- ^ Jar name
                   -> String            -- ^ Conser Type
                   -> String            -- ^ Ontology
                   -> String            -- ^ String
                   -> IO (Result (Conservativity, [Axiom]))
runLocalityChecker jar ct onto sig = do
  (progTh, toolPath) <- check4HetsOWLjar jar
  if progTh then withinDirectory toolPath $ do
      sigFile <- getTempFile sig "ConservativityCheck.sig.owl"
      let tLimit = 800
          ontoFile = sigFile ++ ".onto.owl"
          jargs = ["-jar", jar, "file://" ++ ontoFile, "file://" ++ sigFile, ct]
      writeFile ontoFile onto
      mExit <- timeoutCommand tLimit "java" jargs
      removeFile ontoFile
      removeFile sigFile
      return $ case mExit of
        Just (cont, out, _) -> parseOutput out cont
        Nothing -> fail $ "Timelimit " ++ show tLimit ++ " exceeded"
    else return $ fail $ jar ++ " not found"

parseOutput :: String
            -> ExitCode
            -> Result (Conservativity, [Axiom])
parseOutput ls1 exit = do
  let ls = lines ls1
  case exit of
    ExitFailure 10 -> return (Cons, [])
    ExitFailure 20 -> fail $ unlines ls
    x -> fail $ "Internal program error: " ++ show x ++ "\n" ++ unlines ls
