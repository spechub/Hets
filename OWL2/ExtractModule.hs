{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  $Header$
Copyright   :  Till Mossakowski, Uni Magdeburg 2016
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  till@iws.cs.ovgu.de
Stability   :  provisional
Portability :  portable

OWL 2 module extraction
-}

module OWL2.ExtractModule where

--import OWL2.AS
import OWL2.Sign
import OWL2.MS
import OWL2.ManchesterPrint
import OWL2.ParseOWL
import OWL2.StaticAnalysis

--import qualified Data.Set as Set
--import qualified Data.Map as Map

import Common.Utils
import Common.Result
import Common.ResultT
import Common.AS_Annotation
import Common.GlobalAnnotations
import qualified Common.IRI as IRI

--import Control.Monad
import Control.Monad.Trans
import System.IO.Unsafe

import Common.ExtSign

import Debug.Trace

extractModule :: [IRI.IRI] -> (Sign, [Named Axiom])
                           -> Result (Sign, [Named Axiom])
extractModule syms onto =
  unsafePerformIO $ runResultT $ extractModuleAux syms onto

extractModuleAux :: [IRI.IRI] -> (Sign, [Named Axiom])
                              -> ResultT IO (Sign, [Named Axiom])
extractModuleAux syms onto = do
  let ontology_content = show $ printOWLBasicTheory onto 
   -- should be a string with the ontology from onto, maybe create a G_theory and pretty print it..., show theory
  inFile <- lift $ getTempFile ontology_content "in"
  outFile <- lift $ getTempFile "" "out"
  let args = trace (show syms) $ [inFile, "--extract-module", "-m STAR"] 
             ++ map (\x -> show $ x{IRI.hasAngles = False}) syms ++ ["-o", outFile]
  (_code,_stdout,_stderr) <- trace (show args) $ lift $ executeProcess "owltools" args ""
  -- in outFile is the module, it needs to be parsed, see parseOWL in ParseOWLAsLibDefn.hs, convert a LIB_DEFN to a theory...
  (_imap,ontos) <- parseOWL False outFile
  -- do liftR for lifting something from Result to ResultT
  case ontos of
   [modOnto] -> do 
     (_ontodoc, ExtSign sig _, sens) <- trace (show modOnto) $ liftR $ basicOWL2Analysis (modOnto, emptySign, emptyGlobalAnnos) 
     lift $ return (sig, sens)
   _ -> error "the module should be just one ontology"


