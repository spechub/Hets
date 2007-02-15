{- |
Module      :  $Header$
Copyright   :  (c)  Daniel Pratsch and Uni Bremen 2002-2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  M.Roggenbach@swansea.ac.uk
Stability   :  provisional
Portability :  portable

abstract syntax of CSP-CASL

-}

module CspCASL.AS_CSP_CASL where

import Common.AnnoState
import Common.Doc
import Common.DocUtils

import CspCASL.AS_CspCASL_Process (PROCESS (..),
                                   PROCESS_DEFN (..),
                                   CHANNEL_DECL(..),
                                  )

basicCspCaslCSpec :: AParser st Basic_CSP_CASL_C_SPEC
basicCspCaslCSpec = do { return (Basic_csp_casl_c_spec (Channel_items []) (Process Skip))
                       }

data Basic_CSP_CASL_C_SPEC = Basic_csp_casl_c_spec CHANNEL_DECL PROCESS_DEFN
                           deriving Show

instance Pretty Basic_CSP_CASL_C_SPEC where
    pretty _ = text ""

