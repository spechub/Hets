{- **********************************************************************

   $Source$

   $Date$
   $Revision$
   Author: Daniel Pratsch (Last modification by $Author$)

  ************************************************************************** 
-}

module AS_CSP_CASL where

import AS_Basic_CASL
import Id

----------------------------------------------------------------------------
-- DATA, CHANNEL & PROCESS Def.
----------------------------------------------------------------------------

--data NAMED_CSP_CASL_C_SPEC =  Named_csp_casl_spec SPEC_NAME CSP_CASL_C_SPEC
--		   deriving (Show,Eq)

data CSP_CASL_C_SPEC = Csp_casl_c_spec DATA_DEFN CHANNEL_DECL PROCESS_DEFN
		   deriving (Show,Eq)

type DATA_DEFN = BASIC_SPEC           -- will become a structured spec later

data CHANNEL_DECL = Channel_items [CHANNEL_ITEM]
		   deriving (Show,Eq)

data CHANNEL_ITEM = Channel_decl [CHANNEL_NAME] SORT
		   deriving (Show,Eq)

type CHANNEL_NAME = SIMPLE_ID

type PROCESS_NAME = SIMPLE_ID

data PROCESS_DEFN = Basic PROCESS
                  | Recursive [PROCESS_EQN] NAMED_PROCESS
                  | Gen_recursive [PROCESS_EQN] GEN_NAMED_PROCESS
		   deriving (Show,Eq)

data PROCESS      = Named_process NAMED_PROCESS 
                  | Gen_named_process GEN_NAMED_PROCESS
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
                  | Conditional_process FORMULA PROCESS 
                  | Conditional_choice FORMULA PROCESS PROCESS                              
		              | Guarded_command FORMULA PROCESS
                  | Channel_parallel PROCESS CHANNEL_NAME CHANNEL_NAME PROCESS
		   deriving (Show,Eq)


data NAMED_PROCESS = Named_proc PROCESS_NAME 
		   deriving (Show,Eq)

data GEN_NAMED_PROCESS = Gen_named_proc PROCESS_NAME TERM
		   deriving (Show,Eq)

data GEN_PROCESS = Gen_proc PROCESS_NAME VAR EVENT_SET
		   deriving (Show,Eq)

data PROCESS_EQN = Eqn     NAMED_PROCESS PROCESS
                 | Gen_eqn GEN_PROCESS PROCESS
		   deriving (Show,Eq)

data EVENT_SET = ESort SORT
		   deriving (Show,Eq)

data SORT_RENAMING = Op_list [OP_NAME]
		   deriving (Show,Eq)
		   
data CHANNEL_RENAMING = Channel_renaming CHANNEL_NAME CHANNEL_NAME
		   deriving (Show,Eq)
	   
data EVENT        = Term TERM
                  | Send CHANNEL_NAME TERM 
                  | Receive CHANNEL_NAME VAR SORT
		   deriving (Show,Eq)


--data CSP_RENAMING = PRED_NAME
 
--data CSP_RENAMING = SORT_RENAMING
--                  | CHANNEL_RENAMING
--		   deriving (Show,Eq)