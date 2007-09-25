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

import Common.Id (Id)

import CASL.AS_Basic_CASL (VAR)
import CspCASL.AS_CspCASL_Process (EVENT_SET, PROCESS, PROCESS_NAME)

data CspBasicSpec = CspBasicSpec
    { channels :: [CHANNEL]
    , processes :: [PROC_EQ]
    } deriving Show

data CHANNEL = Channel
    { channelNames :: [Id],
      channelSort :: Id
    } deriving Show

--data CHANNEL_DECL = Channel_items [CHANNEL_ITEM]
--                   deriving Show
--
--data CHANNEL_ITEM = Channel_decl [CHANNEL_NAME] SORT
--                   deriving Show
--
--type CHANNEL_NAME = Id

data PROC_EQ = ProcEq PARM_PROCNAME PROCESS
    deriving Show

data PARM_PROCNAME = ParmProcname PROCESS_NAME [PARG_DECL]
    deriving Show

data PARG_DECL = PargDecl [VAR] EVENT_SET
    deriving Show
