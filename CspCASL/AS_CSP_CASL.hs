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

import Common.Doc
import Common.DocUtils
import CASL.AS_Basic_CASL (SORT)
import Common.Id

data Basic_CSP_CASL_C_SPEC = Basic_csp_casl_c_spec CHANNEL_DECL PROCESS_DEFN
                           deriving Show

instance Pretty Basic_CSP_CASL_C_SPEC where
    pretty _ = text ""

data CHANNEL_DECL = Channel_items [CHANNEL_ITEM]
                   deriving Show

data CHANNEL_ITEM = Channel_decl [CHANNEL_NAME] SORT
                   deriving Show

type CHANNEL_NAME = SIMPLE_ID

data PROCESS_DEFN = Basic PROCESS
                  deriving Show

data PROCESS = Skip
             deriving Show
