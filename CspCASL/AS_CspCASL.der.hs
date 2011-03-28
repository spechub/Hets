{- |
Module      :  $Header$
Description :  Abstract syntax fo CspCASL
Copyright   :  (c) Markus Roggenbach and Till Mossakowski and Uni Bremen 2004
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  a.m.gimblett@swan.ac.uk
Stability   :  provisional
Portability :  portable

Abstract syntax of CSP-CASL processes.

-}
module CspCASL.AS_CspCASL where

import Common.Id

import CASL.AS_Basic_CASL (SORT, VAR, VAR_DECL)
import Common.AS_Annotation (Annoted)
import CspCASL.AS_CspCASL_Process

-- DrIFT command
{-! global: GetRange !-}

data CspBasicExt
  = Channels [Annoted CHANNEL_DECL]
  | ProcItems [Annoted PROC_ITEM]
  deriving Show

data CHANNEL_DECL = ChannelDecl [CHANNEL_NAME] SORT deriving Show

data PROC_ITEM
  = Proc_Decl PROCESS_NAME PROC_ARGS PROC_ALPHABET
  | Proc_Defn PROCESS_NAME [VAR_DECL] PROC_ALPHABET PROCESS
  | Proc_Eq PARM_PROCNAME PROCESS
    deriving Show

data PARM_PROCNAME
  = ParmProcname FQ_PROCESS_NAME [VAR]
    deriving Show
