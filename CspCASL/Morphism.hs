{- |
Module      :  $Header$
Description :  Symbols and signature morphisms for the CspCASL logic
Copyright   :  (c) Liam O'Reilly, Markus Roggenbach, Swansea University 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  csliam@swansea.ac.uk
Stability   :  provisional
Portability :  portable

Symbols and signature morphisms for the CASL logic
-}

module CspCASL.Morphism where

import CASL.Sign
import Common.Id(simpleIdToId)
import CspCASL.SignCSP

import qualified Data.Map as Map
import qualified Data.Set as Set

-- | Calculate the set of symbols for a CspCASL signature
symOf :: CspCASLSign -> Set.Set Symbol
symOf sigma =
    let caslSymbols = symOf sigma -- Get CASL symbols
        cspExt = extendedInfo sigma
        chanNames = Set.fromList $ Map.keys (chans cspExt) -- Get the channel names
        procNames = Set.fromList $ Map.keys (procSet cspExt) -- Get the process names
        mkChanSymbol c = Symbol {
                           symName = simpleIdToId c,
                           symbType = OtherTypeKind "CHANNEL_KIND"
                         }
        mkProcNameSymbol p = Symbol {
                               symName = simpleIdToId p,
                               symbType = OtherTypeKind "PROC_NAME_KIND"
                             }
        -- Make channel symbols from names
        chanSymbols = Set.map mkChanSymbol chanNames
        -- Make process name symbols from names
        procNameSymbols = Set.map mkProcNameSymbol procNames
    in Set.unions [caslSymbols, chanSymbols, procNameSymbols]