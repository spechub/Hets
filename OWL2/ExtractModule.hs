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

import OWL2.AS
import OWL2.Sign
import OWL2.MS

import qualified Data.Set as Set
import qualified Data.Map as Map

import Common.Utils
import Common.Result
import Common.ResultT
import Common.AS_Annotation
import qualified Common.IRI as IRI

import Control.Monad
import Control.Monad.Trans
import System.IO.Unsafe

extractModule :: [IRI.IRI] -> (Sign, [Named Axiom])
                           -> Result (Sign, [Named Axiom])
extractModule syms onto =
  unsafePerformIO $ runResultT $ extractModuleAux syms onto

extractModuleAux :: [IRI.IRI] -> (Sign, [Named Axiom])
                              -> ResultT IO (Sign, [Named Axiom])
extractModuleAux syms onto = do
  let ontolgy_content = "Class: A"
  inFile <- lift $ getTempFile ontolgy_content "owl"
  outFile <- lift $ getTempFile "" "owl"
  let args = [inFile, "--extract-module", "-d"] 
             ++ map show syms ++ ["-o", outFile]
  (code,stdout,stderr) <- lift $ executeProcess "owltools" args ""
  lift $ return onto


