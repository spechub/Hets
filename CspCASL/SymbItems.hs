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

import CASL.AS_Basic_CASL

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

instance Pretty SymbItems

instance Pretty SymbMapItems
