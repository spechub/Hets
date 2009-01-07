{- |
Module      :  $Header$
Description : simplification of CspCASL sentences for output after analysis
Copyright   :  (c) Liam O'Reilly and Markus Roggenbach, Swansea University 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  csliam@swansea.ac.uk
Stability   :  provisional
Portability :  portable

Simplification of CspCASL sentences for output after analysis

-}

module CspCASL.SimplifySen(simplifySen) where

import CASL.SimplifySen (simplifyCASLSen)

import CspCASL.AS_CspCASL_Process
import CspCASL.SignCSP

-- | Simplify a CspCASL sentence for before pretty printing, e.g. for
-- | "show theory". typically this replaces fully quallified CASL by
-- | non fully qualified CASL so that it is readable.
simplifySen :: CspCASLSign -> CspCASLSen -> CspCASLSen
simplifySen sigma sen =
    case sen of
      CASLSen f ->
          let caslSign = ccSig2CASLSign sigma
          in CASLSen $ simplifyCASLSen caslSign f
      ProcessEq pn var alpha p -> ProcessEq pn var alpha ( p) -- (simplifyProc sigma p)

simplifyProc :: CspCASLSign -> PROCESS -> PROCESS
simplifyProc sigma proc =
    let caslSign = ccSig2CASLSign sigma
    in case proc of
      Skip range ->
          Skip range
      Stop range ->
          Stop range
      Div range ->
          Div range
      Run es range ->
          Run es range
      Chaos es range ->
          Chaos es range
      PrefixProcess e p range ->
          PrefixProcess e (simplifyProc sigma p) range
      ExternalPrefixProcess v s p range ->
          ExternalPrefixProcess v s (simplifyProc sigma p) range
      InternalPrefixProcess v s p range ->
          InternalPrefixProcess v s (simplifyProc sigma p) range
      Sequential p q range ->
          Sequential (simplifyProc sigma p) (simplifyProc sigma q) range
      ExternalChoice p q range ->
          ExternalChoice (simplifyProc sigma p) (simplifyProc sigma q) range
      InternalChoice p q range ->
          InternalChoice (simplifyProc sigma p) (simplifyProc sigma q) range
      Interleaving p q range ->
          Interleaving (simplifyProc sigma p) (simplifyProc sigma q) range
      SynchronousParallel p q range ->
          SynchronousParallel (simplifyProc sigma p) (simplifyProc sigma q) range
      GeneralisedParallel p es q range ->
          GeneralisedParallel (simplifyProc sigma p) es (simplifyProc sigma q) range
      AlphabetisedParallel p esp esq q range ->
          AlphabetisedParallel (simplifyProc sigma p) esp esq (simplifyProc sigma q) range
      Hiding p es range ->
          Hiding (simplifyProc sigma p) es range
      RenamingProcess p r range ->
          RenamingProcess (simplifyProc sigma p) r range
      ConditionalProcess f p q range ->
          ConditionalProcess (simplifyCASLSen caslSign f)
                                 (simplifyProc sigma p) (simplifyProc sigma q) range
      NamedProcess name args range ->
          NamedProcess name args range
      FQProcess p alpha range ->
          FQProcess (simplifyProc sigma p) alpha range

