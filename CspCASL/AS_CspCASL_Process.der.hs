{- |
Module      :  $Id$
Description :  Abstract syntax of CSP-CASL processes
Copyright   :  (c) Markus Roggenbach and Till Mossakowski and Uni Bremen 2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  a.m.gimblett@swan.ac.uk
Stability   :  provisional
Portability :  portable

Abstract syntax of CSP-CASL processes.

-}

module CspCASL.AS_CspCASL_Process (
    CHANNEL_NAME,
    COMM_TYPE,
    EVENT(..),
    EVENT_SET(..),
    PROCESS(..),
    PROCESS_NAME,
    RENAMING,
    CommAlpha,
    CommType(..),
    TypedChanName(..)
) where

import CASL.AS_Basic_CASL (FORMULA, SORT, TERM, VAR)
import Common.Id
import qualified Data.Set as Set

-- DrIFT command
{-! global: GetRange !-}

data EVENT
    = TermEvent (TERM ()) Range
    | ChanSend CHANNEL_NAME (TERM ()) Range
    | ChanNonDetSend CHANNEL_NAME VAR SORT Range
    | ChanRecv CHANNEL_NAME VAR SORT Range
    -- | A fully qualified event contains the event being
    -- | qualified. The channel of the fully qualified event should be
    -- | -- nothing if the contained event is a TermEvent - as this
    -- | does -- not have a channel. The channel should match the
    -- | contained -- event's channel if the contained event is not a
    -- | TermEvent, -- where the sort of the channel is also recorded
    -- | in the pair. The -- fully qualified term's event should be
    -- | the fully qualified -- version of the contained events'
    -- | term. The range of the fully -- qualified event should always
    -- | be the same as the range of the -- contained event. In the
    -- | case of a fully qualified ChanNonDetSend and ChanRecv the
    -- | variable becomes a fully qualified CASL term based on the
    -- | variable and its sort.
    | FQEvent EVENT (Maybe (CHANNEL_NAME, SORT)) (TERM ()) Range
    deriving (Show,Ord, Eq)

-- |Event sets are sets of communication types.

data EVENT_SET = EventSet [COMM_TYPE] Range
    deriving (Show,Ord, Eq)

-- |CSP renamings are predicate names or op names.

type RENAMING = [Id]

type CHANNEL_NAME = SIMPLE_ID

type PROCESS_NAME = SIMPLE_ID

type COMM_TYPE = SIMPLE_ID

-- | A process communication alphabet consists of a set of sort names
-- and typed channel names.
data TypedChanName = TypedChanName CHANNEL_NAME SORT
                     deriving (Eq, Ord, Show)

data CommType = CommTypeSort SORT
              | CommTypeChan TypedChanName
                deriving (Eq, Ord)

instance Show CommType where
    show (CommTypeSort s) = show s
    show (CommTypeChan (TypedChanName c s)) = show (c, s)

type CommAlpha = Set.Set CommType

-- |CSP-CASL process expressions.

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
    -- | @es -> p@ - Prefix process
    | PrefixProcess EVENT PROCESS Range
    -- | @[] var : es -> p@ - External nondeterministic prefix choice
    | ExternalPrefixProcess VAR SORT PROCESS Range
    -- | @|~| var : es -> p@ - Internal nondeterministic prefix choice
    | InternalPrefixProcess VAR SORT PROCESS Range
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
    | NamedProcess PROCESS_NAME [TERM ()] Range
    -- | Fully qualified process. The range here shall be the same as
    -- | in the process.
    | FQProcess PROCESS CommAlpha Range
    deriving (Eq, Ord, Show)
