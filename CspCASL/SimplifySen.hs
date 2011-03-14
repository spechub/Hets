{- |
Module      :  $Header$
Description : simplification of CspCASL sentences for output after analysis
Copyright   :  (c) Liam O'Reilly and Markus Roggenbach, Swansea University 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  csliam@swansea.ac.uk
Stability   :  provisional
Portability :  portable

Simplification of CspCASL sentences for output after analysis

-}

module CspCASL.SimplifySen(simplifySen) where

import CASL.AS_Basic_CASL (TERM (..), OP_SYMB (..))
import CASL.SimplifySen (simplifyCASLSen, simplifyCASLTerm)


import Common.Id (simpleIdToId, nullRange)

import CspCASL.AS_CspCASL_Process
import CspCASL.SignCSP

-- | Simplify a CspCASL sentence for before pretty printing, e.g., for
--   "show theory". Typically this replaces fully quallified CASL by
--   non fully qualified CASL so that it is readable.
simplifySen :: CspCASLSign -> CspCASLSen -> CspCASLSen
simplifySen sigma sen =
    case sen of
      CASLSen f ->
          -- Use the CASL simplifySen function
          let caslSign = ccSig2CASLSign sigma
          in CASLSen $ simplifyCASLSen caslSign f
      ProcessEq pn var alpha p ->
          -- Simpliy the process
          let simpPn = simplifyFQProcName pn
              simpVar = simplifyFQProcVarList var
              simpP = simplifyProc sigma p
          in ProcessEq simpPn simpVar alpha simpP

-- | Simplifies a process name.
simplifyFQProcName :: FQ_PROCESS_NAME -> FQ_PROCESS_NAME
simplifyFQProcName fqPn =
  PROCESS_NAME $ procNameToSimpProcName fqPn

-- | Simplifiy a fully qualified variable list
simplifyFQProcVarList :: FQProcVarList -> FQProcVarList
simplifyFQProcVarList fqvars =
  -- Our fully qualified variable list is a list of CASL terms where each term
  -- is a Qual_var. The CASL simplifier will refuse to simplify these as it
  -- thinks you need the type as there is no application of a function or
  -- predicate around the variable. Thus we do our own stripping.
  let simplify (fqVar) = case fqVar of
        Qual_var v _ _ -> Application (Op_name $ simpleIdToId v) [] nullRange
        _ -> error "CspCASL.SimplifySen.simplifyFQProcVarList:\
                   \ Unexpected CASL term"
    in map simplify fqvars

-- | Simplifies the fully qualified CASL data and simplifies the fully
--   qualified processes down to non-fully qualified processes.
simplifyProc :: CspCASLSign -> PROCESS -> PROCESS
simplifyProc sigma proc =
    let caslSign = ccSig2CASLSign sigma
    in case proc of
      Skip range ->
          Skip range
      Stop range ->
          Stop range
      Div range ->
          Div range
      Run es range ->
          Run (simplifyEventSet es) range
      Chaos es range ->
          Chaos (simplifyEventSet es) range
      PrefixProcess e p range ->
          PrefixProcess (simplifyEvent sigma e) (simplifyProc sigma p) range
      Sequential p q range ->
          Sequential (simplifyProc sigma p) (simplifyProc sigma q) range
      ExternalChoice p q range ->
          ExternalChoice (simplifyProc sigma p) (simplifyProc sigma q) range
      InternalChoice p q range ->
          InternalChoice (simplifyProc sigma p) (simplifyProc sigma q) range
      Interleaving p q range ->
          Interleaving (simplifyProc sigma p) (simplifyProc sigma q) range
      SynchronousParallel p q range ->
          SynchronousParallel (simplifyProc sigma p)
                                  (simplifyProc sigma q) range
      GeneralisedParallel p es q range ->
          GeneralisedParallel (simplifyProc sigma p)
                                  (simplifyEventSet es)
                                  (simplifyProc sigma q) range
      AlphabetisedParallel p esp esq q range ->
          AlphabetisedParallel (simplifyProc sigma p)
                                   (simplifyEventSet esp)
                                   (simplifyEventSet esq)
                                   (simplifyProc sigma q) range
      Hiding p es range ->
          Hiding (simplifyProc sigma p) (simplifyEventSet es) range
      RenamingProcess p r range ->
          RenamingProcess (simplifyProc sigma p) r range
      ConditionalProcess f p q range ->
          ConditionalProcess (simplifyCASLSen caslSign f)
                                 (simplifyProc sigma p)
                                 (simplifyProc sigma q) range
      NamedProcess name args range ->
        let simpName = simplifyFQProcName name
            simpArgs = map (simplifyCASLTerm caslSign) args
        in NamedProcess simpName simpArgs range
      -- Throw away the FQProccess and just take the simplified inner
      -- process. The inner processes range will be equal to this
      -- processes range by construction.
      FQProcess p _ _ ->
          simplifyProc sigma p

-- | Simplifies the fully qualified events but using the casl
--   simplification of data and removed channel qualification.
simplifyEvent :: CspCASLSign -> EVENT -> EVENT
simplifyEvent sigma event =
    case event of
      -- This is a non-fully qualified event anyway.
      TermEvent t r -> TermEvent t r
      -- This is a non-fully qualified event anyway.
      ExternalPrefixChoice v s r -> ExternalPrefixChoice v s r
      -- This is a non-fully qualified event anyway.
      InternalPrefixChoice v s r -> InternalPrefixChoice v s r
      -- This is a non-fully qualified event anyway.
      ChanSend cn t r -> ChanSend cn t r
      -- This is a non-fully qualified event anyway.
      ChanNonDetSend cn v s r -> ChanNonDetSend cn v s r
      -- This is a non-fully qualified event anyway.
      ChanRecv cn v s r -> ChanRecv cn v s r
      -- All the fully qualified data is in the parameters here that
      -- we don't use. e is an non-fully qualified event (which
      -- may contain fully qualfied processes), so we simpliy just e.
      FQEvent e _ _ _ -> simplifyEvent sigma e

-- I am not really sure what to do with the sorts at the moment, can they be
-- compound sorts -- BUG?

-- | Simplifies the fully qualified event sets but using the casl
--   simplification of data and removed channel qualification.
simplifyEventSet :: EVENT_SET -> EVENT_SET
simplifyEventSet eventSet = eventSet
--     case eventSet of
--       -- This is a non-fully qualified event set anyway.
--       EventSet es r -> EventSet es r
--       FQEventSet fqEr r -> simplifyCommTypes fqEr r


-- | Simplify a list of comm types. This is basically undoing the
--   static analysis and chaning sorts and typed channel names back to
--   just a list of identifiers containing mixed channels and
--   sorts. This is why we return an EVENT_SET.
-- simplifyCommTypes :: [CommType] -> Range -> EVENT_SET
-- simplifyCommTypes commTypes r =
--     EventSet (map simplifyCommType commTypes) r
--     where
--       simplifyCommType ct =
--           case ct of
--             CommTypeSort s -> genToken $ show s
--             CommTypeChan (TypedChanName chanName _) -> chanName

