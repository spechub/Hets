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

module CspCASL.Morphism ( symOf,
                          makeChannelNameSymbol,
                          makeProcNameSymbol
                        ) where

import CASL.Sign
import qualified CASL.Morphism as CASL_Morphism
import Common.Id(simpleIdToId)
import CspCASL.AS_CspCASL_Process (CHANNEL_NAME, PROCESS_NAME)
import CspCASL.SignCSP
import CspCASL.CspCASL_Keywords

import qualified Data.Map as Map
import qualified Data.Set as Set

channelNameSymbType :: SymbType
channelNameSymbType = OtherTypeKind channelS

processNameSymbType :: SymbType
processNameSymbType = OtherTypeKind processS

-- | Calculate the set of symbols for a CspCASL signature
symOf :: CspCASLSign -> Set.Set Symbol
symOf sigma =
    let caslSymbols = CASL_Morphism.symOf sigma -- Get CASL symbols
        cspExt = extendedInfo sigma
        chanNames = Map.keysSet (chans cspExt) -- Get the channel names
        procNames = Map.keysSet (procSet cspExt) -- Get the process names
        -- Make channel symbols from names
        chanNameSymbols = Set.map makeChannelNameSymbol chanNames
        -- Make process name symbols from names
        procNameSymbols = Set.map makeProcNameSymbol procNames
    in Set.unions [caslSymbols, chanNameSymbols, procNameSymbols]

makeChannelNameSymbol :: CHANNEL_NAME -> Symbol
makeChannelNameSymbol c =
    Symbol {symName = simpleIdToId c, symbType = channelNameSymbType}

makeProcNameSymbol :: PROCESS_NAME -> Symbol
makeProcNameSymbol p =
    Symbol {symName = simpleIdToId p, symbType = processNameSymbType}
