{- |
Module      :  $Id$
Description :  CspCASL keywords to be used for parsing and printing
Copyright   :  (c) Andy Gimblett and Swansea University 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  a.m.gimblett@swan.ac.uk
Stability   :  provisional
Portability :  portable

String constants for CspCASL keywords to be used for parsing and
printing.

-}

module CspCASL.CspCASL_Keywords where

import Common.Token (casl_reserved_words)

-- | Keywords identifying beginning of channel declaration part.
channelS, channelsS :: String
channelS  = "channel"
channelsS = "channels"

-- | Keyword identifying beginning of process equation part.
processS :: String
processS = "process"

-- | interleaving parallel operator
interleavingS :: String
interleavingS = "|||"

-- | synchronous parallel operator
synchronousS :: String
synchronousS = "||"

-- | Open generalised parallel
general_parallel_openS :: String
general_parallel_openS = "[|"

-- | Close generalised parallel
general_parallel_closeS :: String
general_parallel_closeS = "|]"

-- | Open alpabetised parallel
alpha_parallel_openS :: String
alpha_parallel_openS = "["

-- | Separator in alpabetised parallel
alpha_parallel_sepS :: String
alpha_parallel_sepS = "||"

-- | Close alpabetised parallel
alpha_parallel_closeS :: String
alpha_parallel_closeS = "]"

-- | External choice
external_choiceS :: String
external_choiceS = "[]"

-- | Internal choice
internal_choiceS :: String
internal_choiceS = "|~|"

-- | Prefix processes
prefixS :: String
prefixS = "->"

-- | External prefix opener
external_prefixS :: String
external_prefixS = "[]"

-- | Internal prefix opener
internal_prefixS :: String
internal_prefixS = "|~|"

-- | Hiding
hidingS :: String
hidingS = "\\"

-- | Open a renaming
renaming_openS :: String
renaming_openS = "[["

-- | Close a renaming
renaming_closeS :: String
renaming_closeS = "]]"

-- | "RUN" primitive process
runS :: String
runS = "RUN"

-- | "CHAOS" primitive process
chaosS :: String
chaosS = "CHAOS"

-- | "div" primitive process
divS :: String
divS = "div"

-- | "SKIP" primitive process
skipS :: String
skipS = "SKIP"

-- | "STOP" primitive process
stopS :: String
stopS = "STOP"

chan_event_openS :: String
chan_event_openS = "{|"

chan_event_closeS :: String
chan_event_closeS = "|}"

chan_sendS :: String
chan_sendS = "!"

chan_receiveS :: String
chan_receiveS = "?"

svar_sortS :: String
svar_sortS = "@"

-- | Reserved keywords specific to CSP-CASL.
csp_casl_keywords :: [String]
csp_casl_keywords = casl_reserved_words ++
                    [ channelS,
                      channelsS,
                      processS,
                      interleavingS,
                      synchronousS,
                      general_parallel_openS,
                      general_parallel_closeS,
                      alpha_parallel_openS,
                      alpha_parallel_sepS,
                      alpha_parallel_closeS,
                      external_choiceS,
                      internal_choiceS,
                      prefixS,
                      external_prefixS,
                      internal_prefixS,
                      hidingS,
                      renaming_openS,
                      renaming_closeS,
                      runS,
                      chaosS,
                      divS,
                      skipS,
                      stopS,
                      chan_event_openS,
                      chan_event_closeS,
                      chan_sendS,
                      chan_receiveS,
                      svar_sortS
                    ]
