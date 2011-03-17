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

import Common.Doc
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

instance Pretty CspSymbType where
  pretty t = case t of
    CaslSymbType c -> colon <> pretty c
    ProcAsItemType p -> pretty p
    ChanAsItemType s -> colon <+> pretty s

instance Pretty CspSymbol where
  pretty (CspSymbol i t) = pretty i <+> pretty t

instance GetRange CspSymbol where
  getRange (CspSymbol i _) = getRange i

instance Pretty CspRawSymbol where
  pretty r = case r of
    ACspSymbol s -> pretty s
    CspKindedSymb k i -> pretty k <+> pretty i

instance GetRange CspRawSymbol where
  getRange r = case r of
    ACspSymbol s -> getRange s
    CspKindedSymb _ i -> getRange i
