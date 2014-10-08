{-# LANGUAGE DeriveDataTypeable #-}
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
import Common.AS_Annotation (Annoted)

import CASL.AS_Basic_CASL (SORT, VAR, VAR_DECL)

import CspCASL.AS_CspCASL_Process

import Data.Data

-- DrIFT command
{-! global: GetRange !-}

data CspBasicExt
  = Channels [Annoted CHANNEL_DECL] Range
  | ProcItems [Annoted PROC_ITEM] Range
  deriving (Show, Typeable, Data)

data CHANNEL_DECL = ChannelDecl [CHANNEL_NAME] SORT
  deriving (Show, Typeable, Data)

data PROC_ITEM
  = Proc_Decl PROCESS_NAME PROC_ARGS PROC_ALPHABET
  | Proc_Defn PROCESS_NAME [VAR_DECL] PROC_ALPHABET PROCESS
  | Proc_Eq PARM_PROCNAME PROCESS
    deriving (Show, Typeable, Data)

data PARM_PROCNAME
  = ParmProcname FQ_PROCESS_NAME [VAR]
    deriving (Show, Typeable, Data)
