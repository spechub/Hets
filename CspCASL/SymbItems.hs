module CspCASL.SymbItems where

import CspCASL.AS_CspCASL_Process

import CASL.AS_Basic_CASL

import Common.Id

data SymbItems = SymbItems SymbKind [Symb] deriving (Show, Eq)

data SymbMapItems = SymbMapItems SymbKind [SymbMap] deriving (Show, Eq)

data SymbKind = CaslKind SYMB_KIND | ProcessKind | ChannelKind
    deriving (Show, Eq, Ord)

data Symb = Symb Id (Maybe SymbType)
            deriving (Show, Eq)

-- for channels with sorts we may re-use A_type that is ambiguous
data SymbType = CaslType TYPE | ProcType ProcProfile deriving (Show, Eq)

data SymbMap = SymbMap Symb (Maybe Symb) deriving (Show, Eq)
