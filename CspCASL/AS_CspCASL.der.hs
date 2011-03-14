{- |
Module      :  $Id$
Description :  Abstract syntax fo CspCASL
Copyright   :  (c) Markus Roggenbach and Till Mossakowski and Uni Bremen 2004
License     :  GPLv2 or higher, see LICENSE.txt

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
import Common.AS_Annotation(Annoted (..))
import CspCASL.AS_CspCASL_Process (CHANNEL_NAME, PROC_ARGS, PROC_ALPHABET,
                                   PROCESS(..), SIMPLE_PROCESS_NAME,
                                   FQ_PROCESS_NAME)

-- DrIFT command
{-! global: GetRange !-}

data CspBasicSpec = CspBasicSpec
    { channels :: [CHANNEL_DECL]
    , proc_items :: [Annoted PROC_ITEM]
    } deriving Show

data CHANNEL_DECL = ChannelDecl [CHANNEL_NAME] SORT
                    deriving Show

data PROC_ITEM = Proc_Decl SIMPLE_PROCESS_NAME PROC_ARGS PROC_ALPHABET
               | Proc_Eq PARM_PROCNAME PROCESS
                 deriving Show

data PARM_PROCNAME = ParmProcname FQ_PROCESS_NAME [VAR]
                     deriving Show
