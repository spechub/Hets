{- |

Abstract syntax of CSP-CASL processes.

-}

module CspCASL.AS_CspCASL_Process (
    EVENT(..),
    EVENT_SET(..),
    CSP_FORMULA(..),
    PRIMITIVE_RENAMING,
    PROCESS(..),
    PROCESS_DEFN(..),
    PROCESS_NAME,
    REC_PROCESS(..),
    REC_PROCESS_DEFN(..),
    CHANNEL_DECL(..),
    CHANNEL_ITEM(..),
    CHANNEL_NAME
) where

import Common.Id (Id, SIMPLE_ID)
import CASL.AS_Basic_CASL (SORT, TERM, VAR, VAR_DECL)
import qualified CASL.AS_Basic_CASL



{- PROCESS-DEFN ::=   PROCESS
                    | REC-PROCESS
                    | var/vars VAR-DECL; ...; VAR-DECL;/ . PROCESS
                    | var/vars VAR-DECL; ...; VAR-DECL;/ . REC-PROCESS
-}
data PROCESS_DEFN
    = Process PROCESS
    | RecProcess REC_PROCESS
    | ProcessVars [VAR_DECL] PROCESS
    | RecProcessVars [VAR_DECL] PROCESS
    deriving (Show)


{- REC-PROCESS ::= let REC-PROCESS_DEFN; ...; REC-PROCESS-DEFN;/ in PROCESS
-}

data REC_PROCESS
    = RecProcessConstructor [REC_PROCESS_DEFN] PROCESS
    deriving (Show)


{- REC-PROCESS-DEFN ::=   PROCESS-NAME = PROCESS
                        | PROCESS-NAME (VAR: EVENT-SET) = PROCESS
-}

data REC_PROCESS_DEFN
    = RecProcessSimple PROCESS_NAME PROCESS
    | RecProcessVar PROCESS_NAME VAR EVENT_SET PROCESS
    deriving (Show)

-- |Events.  These are CASL terms.  The old CSP-CASL parser also
-- included "Send" and "Receive" forms (commented out below), which I
-- suspect will become important when we bring in channels.

data EVENT
    = Event (TERM ())
    -- Send CHANNEL_NAME (TERM ()) 
    -- Receive CHANNEL_NAME VAR SORT
    deriving (Show,Eq)



-- |Event sets.  These are basically just CASL sorts.

data EVENT_SET
    = EventSet SORT
    deriving (Show,Eq)



-- |Formulas.  These are basically just CASL formulas.

data CSP_FORMULA
    = Formula (CASL.AS_Basic_CASL.FORMULA ())
    deriving (Show,Eq)



-- |CSP renamings.  Just Ids, for operator names and predicate
-- names.

type PRIMITIVE_RENAMING = Id



{- PROCESS_NAME ::= SIMPLE-ID
-}
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
    -- | @[] var : es -> p@ - Internal nondeterministic prefix choice
    | InternalPrefixProcess VAR EVENT_SET PROCESS
    -- | @|~| var : es -> p@ - External nondeterministic prefix choice
    | ExternalPrefixProcess VAR EVENT_SET PROCESS
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
    | Renaming PROCESS PRIMITIVE_RENAMING
    -- | @if f then p else q@ - Conditional
    | ConditionalProcess CSP_FORMULA PROCESS PROCESS
    --  | CSPSeq [PROCESS]
    deriving (Eq, Show)


-- We don't do anything with channels yet, but we need their
-- declaration to fit in with hets machinery, for now at least.

data CHANNEL_DECL = Channel_items [CHANNEL_ITEM]
                   deriving Show

data CHANNEL_ITEM = Channel_decl [CHANNEL_NAME] SORT
                   deriving Show

type CHANNEL_NAME = SIMPLE_ID
