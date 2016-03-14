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

import Common.Result
import Common.ResultT
import Common.AS_Annotation
import qualified Common.IRI as IRI

import Control.Monad
import System.IO.Unsafe

extractModule :: [IRI.IRI] -> (Sign, [Named Axiom])
                          -> Result (Sign, [Named Axiom])
extractModule sig onto =
  unsafePerformIO $ runResultT $ extractModuleAux sig onto

extractModuleAux :: [IRI.IRI] -> (Sign, [Named Axiom])
                          -> ResultT IO (Sign, [Named Axiom])
extractModuleAux _ = liftR . return


