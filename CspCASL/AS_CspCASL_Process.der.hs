{- |
Module      :  $Id$
Description :  Abstract syntax of CSP-CASL processes
Copyright   :  (c) Markus Roggenbach and Till Mossakowski and Uni Bremen 2004
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  a.m.gimblett@swan.ac.uk
Stability   :  provisional
Portability :  portable

Abstract syntax of CSP-CASL processes.

-}

module CspCASL.AS_CspCASL_Process (
    CHANNEL_NAME,
    CommAlpha,
    CommType (..),
    COMM_TYPE,
    EVENT (..),
    EVENT_SET (..),
    FQ_PROCESS_NAME (..),
    PROCESS (..),
    PROC_ARGS,
    PROC_ALPHABET (..),
    procNameToSimpProcName,
    ProcProfile (..),
    RENAMING (..),
    SIMPLE_PROCESS_NAME,
    TypedChanName (..)
) where

import CASL.AS_Basic_CASL (FORMULA, SORT, TERM, VAR)
import Common.Id
import qualified Data.Set as Set

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
    -- | A fully qualified event contains the (non-fully qualified)
    -- event being qualified. There other parameters depend on the
    -- underlying type of the event.
    -- -
    -- For TermEvent, the fully qualified channel should be nothing
    -- and the fully qualified term should be the fully qualified
    -- CASL term version of the term being communicated in the inner
    -- process.
    -- -
    -- For ExternalPrefixChoice and InternalPrefixChoice, the fully
    -- qualified channel should be nothing and the fully qualified
    -- term should be the fully qualified CASL variable version (a
    -- term) of the inner process's variable.
    -- -
    -- For ChanSend, the fully qualified channel should be the fully
    -- qualified channel of the underlying event and the fully
    -- qualified term should be the fully qualified CASL term
    -- version of the term being communicated in the inner process.
    -- -
    -- For ChanNonDetSend and ChanRecv, the fully qualified channel
    -- should be the fully qualified channel of the underlying event
    -- and the fully qualified CASL variable version (a term) of the
    -- inner process's variable
    | FQEvent EVENT (Maybe (CHANNEL_NAME, SORT)) (TERM ()) Range
    deriving (Show, Ord, Eq)

-- | Event sets are sets of communication types.
data EVENT_SET = EventSet [COMM_TYPE] Range
               -- | FQEvent set distinguishes between channel names and Sorts
               | FQEventSet [CommType] Range
                 deriving (Show, Ord, Eq)

-- | CSP renamings are predicate names or op names.
data RENAMING = Renaming [Id]
              | FQRenaming [TERM ()]
                deriving (Show, Ord, Eq)

type CHANNEL_NAME = SIMPLE_ID

type SIMPLE_PROCESS_NAME = SIMPLE_ID

type PROC_ARGS = [SORT]

data PROC_ALPHABET = ProcAlphabet [COMM_TYPE] Range
                     deriving (Show,Ord, Eq)

-- | Fully qualified process names are indexed by parameter sorts, and a
-- communication alphabet (a Set of sorts). The CommAlpha here should always
-- contain downward closed sets (wrt the subsort relation).
data ProcProfile = ProcProfile [SORT] CommAlpha
                   deriving (Eq, Ord, Show)

-- | A process name is either a fully qualified process name or a plain process
-- name.
data FQ_PROCESS_NAME =
  -- | A non-fully qualified process name
  PROCESS_NAME SIMPLE_PROCESS_NAME
  -- | A fully qualified process name
  | FQ_PROCESS_NAME SIMPLE_PROCESS_NAME ProcProfile
  -- | A name with parameter sorts and communication ids from the parser.
  -- This is where the user has tried to specify a fully qualified process name
  | PARSED_FQ_PROCESS_NAME SIMPLE_PROCESS_NAME PROC_ARGS PROC_ALPHABET
                  deriving (Eq, Ord, Show)

procNameToSimpProcName :: FQ_PROCESS_NAME -> SIMPLE_PROCESS_NAME
procNameToSimpProcName (PROCESS_NAME pn) = pn
procNameToSimpProcName (FQ_PROCESS_NAME pn _ ) = pn
procNameToSimpProcName (PARSED_FQ_PROCESS_NAME pn _ _) = pn

type COMM_TYPE = SIMPLE_ID

-- | A process communication alphabet consists of a set of sort names
-- and typed channel names.
data TypedChanName = TypedChanName CHANNEL_NAME SORT
                     deriving (Eq, Ord, Show)

data CommType = CommTypeSort SORT
              | CommTypeChan TypedChanName
                deriving (Eq, Ord)

-- | Type of communication types, either a sort communication or a typed channel
-- communications.
instance Show CommType where
    show (CommTypeSort s) = show s
    show (CommTypeChan (TypedChanName c s)) = show (c, s)

-- | Type of communication alphabet
type CommAlpha = Set.Set CommType

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
    -- | Fully qualified process. The range here shall be the same as
    -- | in the process.
    | FQProcess PROCESS CommAlpha Range
    deriving (Eq, Ord, Show)
