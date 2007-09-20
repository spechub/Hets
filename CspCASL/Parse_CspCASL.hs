{- |
Module      :  $Id$
Description :  Parser for CspCASL specifications
Copyright   :  (c) 
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  a.m.gimblett@swan.ac.uk
Stability   :  experimental
Portability :  

Parser for CSP-CASL specifications.

-}

module CspCASL.Parse_CspCASL (
    processPart
) where

import Common.AnnoState (AParser, asKey)

import CspCASL.AS_CspCASL
import CspCASL.CspCASL_Keywords
import CspCASL.Parse_CspCASL_Process (csp_casl_process)

processPart :: AParser st PROCESS_PART
processPart = do asKey processS
                 p <- csp_casl_process
                 return (ProcessPart p)
