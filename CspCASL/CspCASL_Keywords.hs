{- |
Module      :  $Header$
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

doubleSemis :: String
doubleSemis = ";;"

-- | starting CSP-CASL keywords
startCspKeywords :: [String]
startCspKeywords =
  [ channelS
  , channelS ++ "s"
  , processS
  , processS ++ "es" ]

-- | Reserved keywords specific to CSP-CASL.
cspKeywords :: [String]
cspKeywords = startCspKeywords ++
  [ -- sequentialS
  doubleSemis -- we add this as alternative sequential composition operator
  , interleavingS
  , synchronousS
{- , genpar_openS
  , genpar_closeS -}
  , alpar_openS
-- , alpar_sepS -- is identical to synchronousS
  , alpar_closeS
-- , external_choiceS
  , internal_choiceS
  , prefix_procS
  , hiding_procS
{- , ren_proc_openS
  , ren_proc_closeS -}
  , barS -- in case we want to use it within generialized parallel
  , runS
  , chaosS
  , divS
  , skipS
  , stopS
{- , chan_sendS
  , chan_receiveS -}
  , svar_sortS ]
