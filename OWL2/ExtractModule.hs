{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./OWL2/ExtractModule.hs
Copyright   :  Till Mossakowski, Uni Magdeburg 2016
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  till@iws.cs.ovgu.de
Stability   :  provisional
Portability :  portable

OWL 2 module extraction
-}

module OWL2.ExtractModule where

import OWL2.Sign
import OWL2.MS
import OWL2.ManchesterPrint
import OWL2.ParseOWL
import OWL2.StaticAnalysis

import Common.Utils
import Common.Result
import Common.ResultT
import Common.AS_Annotation
import Common.GlobalAnnotations
import qualified Common.IRI as IRI

import qualified Data.Map as Map

import Control.Monad.Trans
import System.IO.Unsafe

import Common.ExtSign

extractModule :: [IRI.IRI] -> (Sign, [Named Axiom])
                           -> Result (Sign, [Named Axiom])
extractModule syms onto =
  unsafePerformIO $ runResultT $ extractModuleAux syms onto

extractModuleAux :: [IRI.IRI] -> (Sign, [Named Axiom])
                              -> ResultT IO (Sign, [Named Axiom])
extractModuleAux syms onto@(osig,_) = do
  let ontology_content = show $ printOWLBasicTheory onto
  inFile <- lift $ getTempFile ontology_content "in"
  outFile <- lift $ getTempFile "" "out"
  let args = [inFile, "--extract-module", "-m", "STAR"]
             ++ map (\x -> show $ x{IRI.hasAngles = False}) syms
             ++ ["-o", outFile]
  (_code,_stdout,_stderr) <- lift $ executeProcess "owltools" args ""
  (_imap,ontos) <- parseOWL False outFile
  case ontos of
   [modOnto] -> do
     (_ontodoc, ExtSign sig _, sens) <- liftR $
         basicOWL2Analysis (modOnto, emptySign, emptyGlobalAnnos)
     lift $ return (sig {
                      prefixMap = Map.union (prefixMap osig) 
                                  $ prefixMap sig}, 
                   sens)
   _ -> error "the module should be just one ontology"
