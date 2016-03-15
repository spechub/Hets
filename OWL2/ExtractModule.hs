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

--import qualified Data.Set as Set
--import qualified Data.Map as Map

import Common.Utils
import Common.Result
import Common.ResultT
import Common.AS_Annotation
import qualified Common.IRI as IRI

--import Control.Monad
import Control.Monad.Trans
import System.IO.Unsafe

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
  inFile <- lift $ getTempFile ontology_content "owl"
  outFile <- lift $ getTempFile "" "owl"
  let args = [inFile, "--extract-module", "-d"] 
             ++ map show syms ++ ["-o", outFile]
  (code,stdout,stderr) <- lift $ executeProcess "owltools" args ""
  -- in outFile is the module, it needs to be parsed, see parseOWL in ParseOWLAsLibDefn.hs, convert a LIB_DEFN to a theory...
  (imap,ontos) <- parseOWL False outFile
  -- do liftIO for lifting something from Result to ResultT
  lift $ return onto


