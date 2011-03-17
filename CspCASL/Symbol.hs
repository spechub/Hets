{- |
Module      :  $Header$
Description :  semantic csp-casl symbols
Copyright   :  (c) Christian Maeder, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module CspCASL.Symbol where

import CspCASL.SymbItems
import CspCASL.AS_CspCASL_Process

import CASL.Sign

import Common.DocUtils
import Common.Id

data CspSymbType
  = CaslSymbType SymbType
  | ProcAsItemType ProcProfile
  | ChanAsItemType Id -- the SORT
  deriving (Show, Eq, Ord)

data CspSymbol = CspSymbol {cspSymName :: Id, cspSymbType :: CspSymbType}
  deriving (Show, Eq, Ord)

data CspRawSymbol = ACspSymbol CspSymbol | CspKindedSymb SymbKind Id
  deriving (Show, Eq, Ord)

instance Pretty CspSymbol

instance GetRange CspSymbol

instance Pretty CspRawSymbol

instance GetRange CspRawSymbol
