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

-- | Keyword identifying beginning of CSP-CASL spec.
ccspecS :: String
ccspecS = "ccspec"

-- | Keyword identifying beginning of data part of CSP-CASL spec.
dataS :: String
dataS = "data"

-- | Keyword identifying beginning of process part of CSP-CASL spec.
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

-- | Semicolon (sequences of processes)
semicolonS :: String
semicolonS = ";"

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

-- | Open parentheses
parens_openS :: String
parens_openS = "("

-- | Close parentheses
parens_closeS :: String
parens_closeS = ")"

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

-- | Reserved keywords specific to CSP-CASL.
csp_casl_keywords :: [String]
csp_casl_keywords = casl_reserved_words ++
                    [ ccspecS,
                      dataS,
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
                      semicolonS,
                      prefixS,
                      external_prefixS,
                      internal_prefixS,
                      hidingS,
                      renaming_openS,
                      renaming_closeS,
                      parens_openS,
                      parens_closeS,
                      runS,
                      chaosS,
                      divS,
                      skipS,
                      stopS
                    ]
