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
) where

import CASL.AS_Basic_CASL (FORMULA, SORT, TERM, VAR)
import Common.Id

-- DrIFT command
{-! global: GetRange !-}

data EVENT
    = TermEvent (TERM ()) Range
    | ChanSend CHANNEL_NAME (TERM ()) Range
    | ChanNonDetSend CHANNEL_NAME VAR SORT Range
    | ChanRecv CHANNEL_NAME VAR SORT Range
    deriving (Show,Ord, Eq)


-- |Event sets are sets of communication types.

data EVENT_SET = EventSet [COMM_TYPE] Range
    deriving (Show,Ord, Eq)


-- |CSP renamings are predicate names or op names.

type RENAMING = [Id]


type CHANNEL_NAME = SIMPLE_ID

type PROCESS_NAME = SIMPLE_ID

type COMM_TYPE = SIMPLE_ID


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
    deriving (Eq, Ord, Show)
