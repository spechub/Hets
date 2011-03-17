{- |
Module      :  $Id$
Description :  CspCASL keywords to be used for parsing and printing
Copyright   :  (c) Andy Gimblett and Swansea University 2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  a.m.gimblett@swan.ac.uk
Stability   :  provisional
Portability :  portable

String constants for CspCASL keywords to be used for parsing and
printing.

-}

module CspCASL.CspCASL_Keywords where

import Common.Keywords
import Common.Token (casl_reserved_words)

-- | Keywords identifying beginning of channel declaration part.
channelS :: String
channelS = "channel"

-- | Keyword identifying beginning of process equation part.
processS :: String
processS = "process"

-- | "RUN" primitive process
runS :: String
runS = "RUN"

-- | "CHAOS" primitive process
chaosS :: String
chaosS = "CHAOS"

-- | "div" primitive process
divS :: String
divS = "DIV"

-- | "SKIP" primitive process
skipS :: String
skipS = "SKIP"

-- | "STOP" primitive process
stopS :: String
stopS = "STOP"

chan_sendS :: String
chan_sendS = "!"

chan_receiveS :: String
chan_receiveS = "?"

svar_sortS :: String
svar_sortS = "::"

-- | Reserved keywords specific to CSP-CASL.
csp_casl_keywords :: [String]
csp_casl_keywords = casl_reserved_words ++
                    [ channelS,
                      channelS ++ sS,
                      processS,
                      sequentialS,
                      interleavingS,
                      synchronousS,
                      genpar_openS,
                      genpar_closeS,
                      alpar_openS,
                      alpar_sepS,
                      alpar_closeS,
                      external_choiceS,
                      internal_choiceS,
                      prefix_procS,
                      hiding_procS,
                      ren_proc_openS,
                      ren_proc_closeS,
                      runS,
                      chaosS,
                      divS,
                      skipS,
                      stopS,
                      chan_sendS,
                      chan_receiveS,
                      svar_sortS
                    ]
