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
    EVENT(..),
    EVENT_SET(..),
    CSP_FORMULA(..),
    PROCESS(..),
    PROCESS_NAME,
    RENAMING,
) where

import CASL.AS_Basic_CASL (FORMULA, SORT, TERM, VAR)
import Common.Id (Id)



data EVENT
    = Event (TERM ())
    | Send CHANNEL_NAME (TERM ())
    | Receive CHANNEL_NAME VAR SORT
    deriving (Show,Eq)



-- |Event sets.  These are basically just CASL sorts.

data EVENT_SET
    = EventSet { eventSetSort :: SORT }
    | ChannelEvents CHANNEL_NAME
    | EmptyEventSet -- Used for translation to Core-CspCASL
    deriving (Show,Eq)



-- |Formulas.  These are basically just CASL formulas.

data CSP_FORMULA
    = Formula (FORMULA ())
    deriving (Show,Eq)



-- |CSP renamings are predicate names or op names.

type RENAMING = [Id]



type CHANNEL_NAME = Id

type PROCESS_NAME = Id




-- |CSP-CASL process expressions.

data PROCESS
    -- | @Skip@ - Terminate immediately
    = Skip
    -- | @Stop@ - Do nothing
    | Stop
    -- | @div@ - Divergence
    | Div
    -- | @Run es@ - Accept any event in es, forever
    | Run EVENT_SET
    -- | @Chaos es@ - Accept\/refuse any event in es, forever
    | Chaos EVENT_SET
    -- | @es -> p@ - Prefix process
    | PrefixProcess EVENT PROCESS
    -- | @[] var : es -> p@ - External nondeterministic prefix choice
    | ExternalPrefixProcess VAR SORT PROCESS
    -- | @|~| var : es -> p@ - Internal nondeterministic prefix choice
    | InternalPrefixProcess VAR SORT PROCESS
    -- | @p ; q@ - Sequential process
    | Sequential PROCESS PROCESS
    -- | @p [] q@ - External choice
    | ExternalChoice PROCESS PROCESS
    -- | @p |~| q@ - Internal choice
    | InternalChoice PROCESS PROCESS
    -- | @p ||| q@ - Interleaving
    | Interleaving PROCESS PROCESS
    -- | @p || q @ - Synchronous parallel
    | SynchronousParallel PROCESS PROCESS
    -- | @p [| a |] q@ - Generalised parallel
    | GeneralisedParallel PROCESS EVENT_SET PROCESS
    -- | @p [ a || b ] q@ - Alphabetised parallel
    | AlphabetisedParallel PROCESS EVENT_SET EVENT_SET PROCESS
    -- | @p \\ es@ - Hiding
    | Hiding PROCESS EVENT_SET
    -- | @p [[r]]@ - Renaming
    | RelationalRenaming PROCESS RENAMING
    -- | @if f then p else q@ - Conditional
    | ConditionalProcess CSP_FORMULA PROCESS PROCESS
    -- | Named process
    | NamedProcess PROCESS_NAME [EVENT]
    deriving (Eq, Show)
