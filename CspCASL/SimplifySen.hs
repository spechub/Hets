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

import qualified CASL.SimplifySen as CASL_SimplifySen

import CspCASL.SignCSP

simplifySen :: CspCASLSign -> CspCASLSen -> CspCASLSen
simplifySen sigma sen =
    case sen of
      CASLSen f ->
          let caslSign = ccSig2CASLSign sigma
          in CASLSen $ CASL_SimplifySen.simplifyCASLSen caslSign f
      ProcessEq pn var alpha p -> ProcessEq pn var alpha p