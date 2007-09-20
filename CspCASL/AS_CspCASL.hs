{- |
Module      :  $Id$
Description :  Abstract syntax fo CspCASL
Copyright   :  (c) Markus Roggenbach and Till Mossakowski and Uni Bremen 2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  a.m.gimblett@swan.ac.uk
Stability   :  provisional
Portability :  portable

Abstract syntax of CSP-CASL processes.

-}
module CspCASL.AS_CspCASL where

import CASL.AS_Basic_CASL (BASIC_SPEC)
import Common.Id (Id)

import CspCASL.AS_CspCASL_Process (PROCESS)

type CCSPEC_NAME = Id

data BASIC_CSP_CASL_SPEC
    = Basic_Csp_Casl_Spec CCSPEC_NAME DATA_PART PROCESS_PART
    deriving (Show)

data DATA_PART
    = DataPart (BASIC_SPEC () () ())
    deriving (Show)

data PROCESS_PART
    = ProcessPart PROCESS
    deriving (Show)
