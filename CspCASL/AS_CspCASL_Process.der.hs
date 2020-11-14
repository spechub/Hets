{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
{- |
Module      :  ./CspCASL/AS_CspCASL_Process.der.hs
Description :  Abstract syntax of CSP-CASL processes
Copyright   :  (c) Markus Roggenbach and Till Mossakowski and Uni Bremen 2004
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  a.m.gimblett@swan.ac.uk
Stability   :  provisional
Portability :  portable

Abstract syntax of CSP-CASL processes.

-}

module CspCASL.AS_CspCASL_Process
  ( CHANNEL_NAME
  , CommAlpha
  , CommType (..)
  , EVENT (..)
  , EVENT_SET (..)
  , FQ_PROCESS_NAME (..)
  , PROCESS (..)
  , PROCESS_NAME
  , PROC_ARGS
  , PROC_ALPHABET (..)
  , procNameToSimpProcName
  , ProcProfile (..)
  , RenameKind (..)
  , Rename (..)
  , RENAMING (..)
  , splitCASLVar
  , TypedChanName (..)
  ) where

import CASL.AS_Basic_CASL (FORMULA, SORT, TERM (..), VAR)

import Common.Id
import Common.Utils

import Data.Data
import qualified Data.HashSet as Set

import GHC.Generics (Generic)
import Data.Hashable

-- DrIFT command
{-! global: GetRange !-}

data EVENT
    -- | @t -> p@ - Term prefix
    = TermEvent (TERM ()) Range
    -- | @[] var :: s -> p@ - External nondeterministic prefix choice
    | ExternalPrefixChoice VAR SORT Range
    -- | @|~| var :: s -> p@ - Internal nondeterministic prefix choice
    | InternalPrefixChoice VAR SORT Range
    -- | @c ! t -> p@ - Channel send
    | ChanSend CHANNEL_NAME (TERM ()) Range
    -- | @c ! var :: s -> p@ - Channel nondeterministic send
    | ChanNonDetSend CHANNEL_NAME VAR SORT Range
    -- | @c ? var :: s -> p@ - Channel recieve
    | ChanRecv CHANNEL_NAME VAR SORT Range
    -- | @t -> p@ - Fully Qualified Term prefix
    | FQTermEvent (TERM ()) Range
    {- | @[] var :: s -> p@ - Fully Qualified External nondeterministic prefix
    choice. The term here holds the fully qualified variable (name and sort). -}
    | FQExternalPrefixChoice (TERM ()) Range
    {- | @|~| var :: s -> p@ - Fully Qualified Internal nondeterministic prefix
    choice. The term here holds the fully qualified variable (name and sort). -}
    | FQInternalPrefixChoice (TERM ()) Range
    {- | @c ! t -> p@ - Fully Qualified Channel send. The term holds the fully
    term to send. -}
    | FQChanSend (CHANNEL_NAME, SORT) (TERM ()) Range
    {- | @c ! var :: s -> p@ - Fully Qualified Channel nondeterministic
    send. The term here holds the fully qualified variable (name and sort). -}
    | FQChanNonDetSend (CHANNEL_NAME, SORT) (TERM ()) Range
    {- | @c ? var :: s -> p@ - Fully Qualified Channel recieve. The term here
    holds the fully qualified variable (name and sort). -}
    | FQChanRecv (CHANNEL_NAME, SORT) (TERM ()) Range
    deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable EVENT

-- | Event sets are sets of communication types.
data EVENT_SET = EventSet [CommType] Range
                 deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable EVENT_SET

data RenameKind = TotOp | PartOp | BinPred 
 deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable RenameKind

data Rename = Rename Id (Maybe (RenameKind, Maybe (SORT, SORT)))
    deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable Rename

-- | CSP renamings are predicate names or op names.
data RENAMING = Renaming [Rename]
                deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable RENAMING

type CHANNEL_NAME = Id

type PROCESS_NAME = Id

type PROC_ARGS = [SORT]

data PROC_ALPHABET = ProcAlphabet [CommType]
                     deriving (Show, Eq, Ord, Typeable, Data)

splitCASLVar :: TERM () -> (VAR, SORT)
splitCASLVar (Qual_var v s _ ) = (v, s)
splitCASLVar _ =
  error "CspCASL.AS_CspCASL_Process: Can not split non Qual_var CASL Term"

{- | Fully qualified process names have parameter sorts, and a communication
alphabet (a Set of sorts). The CommAlpha here should always contain the minimal
super sorts only. The communication over subsorts is implied -}
data ProcProfile = ProcProfile PROC_ARGS CommAlpha
                   deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable ProcProfile

{- | A process name is either a fully qualified process name or a plain process
name. -}
data FQ_PROCESS_NAME
  -- | A non-fully qualified process name
  = PROCESS_NAME PROCESS_NAME
  {- | A name with parameter sorts and communication ids from the parser.
  This is where the user has tried to specify a fully qualified process name -}
  | FQ_PROCESS_NAME PROCESS_NAME ProcProfile
                  deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable FQ_PROCESS_NAME

procNameToSimpProcName :: FQ_PROCESS_NAME -> PROCESS_NAME
procNameToSimpProcName (PROCESS_NAME pn) = pn
procNameToSimpProcName (FQ_PROCESS_NAME pn _) = pn

{- | A process communication alphabet consists of a set of sort names
and typed channel names. -}
data TypedChanName = TypedChanName CHANNEL_NAME SORT
                     deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable TypedChanName

data CommType = CommTypeSort SORT
              | CommTypeChan TypedChanName
                deriving (Eq, Ord, Typeable, Data, Generic)

instance Hashable CommType

{- | Type of communication types, either a sort communication or a typed channel
communications. -}
instance Show CommType where
    show (CommTypeSort s) = show s
    show (CommTypeChan (TypedChanName c s)) = show (c, s)

-- | Type of communication alphabet
type CommAlpha = Set.HashSet CommType

-- | CSP-CASL process expressions.
data PROCESS
    -- | @Skip@ - Terminate immediately
    = Skip Range
    -- | @Stop@ - Do nothing
    | Stop Range
    -- | @div@ - Divergence
    | Div Range
    -- | @Run es@ - Accept any event in es, forever
    | Run EVENT_SET Range
    -- | @Chaos es@ - Accept\/refuse any event in es, forever
    | Chaos EVENT_SET Range
    -- | @event -> p@ - Prefix process
    | PrefixProcess EVENT PROCESS Range
    -- | @p ; q@ - Sequential process
    | Sequential PROCESS PROCESS Range
    -- | @p [] q@ - External choice
    | ExternalChoice PROCESS PROCESS Range
    -- | @p |~| q@ - Internal choice
    | InternalChoice PROCESS PROCESS Range
    -- | @p ||| q@ - Interleaving
    | Interleaving PROCESS PROCESS Range
    -- | @p || q @ - Synchronous parallel
    | SynchronousParallel PROCESS PROCESS Range
    -- | @p [| a |] q@ - Generalised parallel
    | GeneralisedParallel PROCESS EVENT_SET PROCESS Range
    -- | @p [ a || b ] q@ - Alphabetised parallel
    | AlphabetisedParallel PROCESS EVENT_SET EVENT_SET PROCESS Range
    -- | @p \\ es@ - Hiding
    | Hiding PROCESS EVENT_SET Range
    -- | @p [[r]]@ - Renaming
    | RenamingProcess PROCESS RENAMING Range
    -- | @if f then p else q@ - Conditional
    | ConditionalProcess (FORMULA ()) PROCESS PROCESS Range
    -- | Named process
    | NamedProcess FQ_PROCESS_NAME [TERM ()] Range
    {- | Fully qualified process. The range here shall be the same as
    in the process. -}
    | FQProcess PROCESS CommAlpha Range
    deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable PROCESS
