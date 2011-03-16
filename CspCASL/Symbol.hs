module CspCASL.Symbol where

import CspCASL.SymbItems
import CspCASL.AS_CspCASL_Process

import CASL.Sign

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
