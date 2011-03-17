{- |
Module      :  $Header$
Description :  syntactic csp-casl symbols
Copyright   :  (c) Christian Maeder, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module CspCASL.SymbItems where

import CspCASL.AS_CspCASL_Process
import CspCASL.CspCASL_Keywords
import CspCASL.Print_CspCASL

import CASL.AS_Basic_CASL
import CASL.ToDoc ()

import Common.Doc
import Common.DocUtils
import Common.Id

data SymbItems = SymbItems SymbKind [Symb] deriving (Show, Eq)

data SymbMapItems = SymbMapItems SymbKind [SymbMap] deriving (Show, Eq)

data SymbKind = CaslKind SYMB_KIND | ProcessKind | ChannelKind
    deriving (Show, Eq, Ord)

data Symb = CspSymb Id (Maybe CspType)
            deriving (Show, Eq)

-- for channels with sorts we may re-use A_type that is ambiguous
data CspType = CaslType TYPE | ProcType ProcProfile deriving (Show, Eq)

data SymbMap = SymbMap Symb (Maybe Symb) deriving (Show, Eq)

instance Pretty SymbKind where
  pretty k = case k of
    CaslKind c -> pretty c
    ProcessKind -> keyword processS
    ChannelKind -> keyword channelS

instance Pretty CspType where
  pretty t = case t of
    CaslType c -> colon <> pretty c
    ProcType p -> printProcProfile p

instance Pretty Symb where
  pretty (CspSymb i ms) = pretty i <+> pretty ms

instance Pretty SymbMap where
  pretty (SymbMap s ms) = pretty s <+> case ms of
    Nothing -> empty
    Just t -> mapsto <+> pretty t

instance Pretty SymbItems where
  pretty (SymbItems k syms) = pretty k <+> ppWithCommas syms

instance Pretty SymbMapItems where
  pretty (SymbMapItems k syms) = pretty k <+> ppWithCommas syms
