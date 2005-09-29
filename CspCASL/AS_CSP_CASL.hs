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

import CASL.AS_Basic_CASL
import Common.Id

----------------------------------------------------------------------------
-- Specifications
----------------------------------------------------------------------------
data C3PO = Named_c3po NAMED_CSP_CASL_C_SPEC 
          | C3po CSP_CASL_C_SPEC
                   deriving Show

data NAMED_CSP_CASL_C_SPEC =  Named_csp_casl_spec SPEC_NAME CSP_CASL_C_SPEC
                   deriving Show

type SPEC_NAME = SIMPLE_ID

data CSP_CASL_C_SPEC = Csp_casl_c_spec DATA_DEFN CHANNEL_DECL PROCESS_DEFN
                   deriving Show

data Basic_CSP_CASL_C_SPEC = Basic_csp_casl_c_spec CHANNEL_DECL PROCESS_DEFN
                   deriving Show

----------------------------------------------------------------------------
-- DATA, CHANNEL & PROCESS Def.
----------------------------------------------------------------------------

type DATA_DEFN = BASIC_SPEC () () ()   -- will become a structured spec later

data CHANNEL_DECL = Channel_items [CHANNEL_ITEM]
                   deriving Show

data CHANNEL_ITEM = Channel_decl [CHANNEL_NAME] SORT
                   deriving Show

type CHANNEL_NAME = SIMPLE_ID

type PROCESS_NAME = SIMPLE_ID

data PROCESS_DEFN = Basic PROCESS
                  | Recursive [PROCESS_EQUATION] NAMED_PROCESS
                  | Generic_recursive [PROCESS_EQUATION] GEN_NAMED_PROCESS
                   deriving (Show,Eq)


data NAMED_PROCESS = Named PROCESS_NAME 
                   deriving (Show,Eq)

data GEN_NAMED_PROCESS = Generic_named PROCESS_NAME (TERM ())
                   deriving (Show,Eq)

data GENERIC_EQUATION = Generic PROCESS_NAME VAR EVENT_SET
                   deriving (Show,Eq)

data PROCESS_EQUATION = Equation NAMED_PROCESS PROCESS
                      | Generic_equation GENERIC_EQUATION PROCESS
                   deriving (Show,Eq)


data PROCESS = Named_process NAMED_PROCESS 
             | Generic_named_process GEN_NAMED_PROCESS
             | Skip
             | Stop
             | Prefix EVENT PROCESS
             | Multiple_prefix VAR EVENT_SET PROCESS
             | Sequential [PROCESS]
             | External_choice [PROCESS]
             | Internal_choice [PROCESS]
             | Alphabet_parallel PROCESS EVENT_SET PROCESS
             | General_parallel PROCESS EVENT_SET EVENT_SET PROCESS
             | Synchronous_parallel [PROCESS]
             | Interleaving_parallel [PROCESS]
             | Hiding PROCESS EVENT_SET
             | Csp_sort_renaming PROCESS SORT_RENAMING
             | Csp_channel_renaming PROCESS CHANNEL_RENAMING
             | Conditional_process (FORMULA ()) PROCESS 
             | Conditional_choice (FORMULA ()) PROCESS PROCESS                              
                         | Guarded_command (FORMULA ()) PROCESS
             | Channel_parallel PROCESS CHANNEL_NAME CHANNEL_NAME PROCESS
                   deriving (Show,Eq)


data EVENT_SET = Event_set SORT
                   deriving (Show,Eq)

data SORT_RENAMING = Op_list [OP_NAME]
                   deriving (Show,Eq)
                   
data CHANNEL_RENAMING = Channel_renaming CHANNEL_NAME CHANNEL_NAME
                   deriving (Show,Eq)
           
data EVENT        = Term (TERM ())
                  | Send CHANNEL_NAME (TERM ()) 
                  | Receive CHANNEL_NAME VAR SORT
                   deriving (Show,Eq)


--data CSP_RENAMING = PRED_NAME
 
--data CSP_RENAMING = SORT_RENAMING
--                  | CHANNEL_RENAMING
--                 deriving (Show,Eq)
