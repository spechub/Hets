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

import Common.Doc()
import Common.DocUtils()
import Common.Id

import CASL.AS_Basic_CASL (SORT, VAR)

import CspCASL.AS_CspCASL_Process (CHANNEL_NAME, COMM_TYPE, PROCESS(..),
                                   PROCESS_NAME)

-- DrIFT command
{-! global: GetRange !-}

data CspBasicSpec = CspBasicSpec
    { channels :: [CHANNEL_DECL]
    , proc_items :: [PROC_ITEM]
    } deriving Show

data CHANNEL_DECL = ChannelDecl [CHANNEL_NAME] SORT
                    deriving Show

data PROC_ALPHABET = ProcAlphabet [COMM_TYPE] Range
                     deriving (Show,Ord, Eq)

data PROC_ITEM = Proc_Decl PROCESS_NAME PROC_ARGS PROC_ALPHABET
               | Proc_Eq PARM_PROCNAME PROCESS
                 deriving Show

type PROC_ARGS = [SORT]

data PARM_PROCNAME = ParmProcname PROCESS_NAME [VAR]
                     deriving Show
