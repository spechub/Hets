{- |
Module      :  $Id$
Description :  Conversion to core CspCASL
Copyright   :  (c) Andy Gimblett and Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  a.m.gimblett@swansea.ac.uk
Stability   :  provisional
Portability :  portable

Converting sugared CspCASL to core CspCASL.

The following process types are core:

  Skip
  Stop
  PrefixProcess ev p
  ExternalPrefixProcess v es p
  InternalPrefixProcess v es p
  Sequential p q
  ExternalChoice p q
  InternalChoice p q
  GeneralisedParallel p es q
  Hiding p es
  RelationalRenaming p RENAMING
  NamedProcess pn evs
  ConditionalProcess CSP_FORMULA p q
 
  (Also the interrupt operator should be added, and core?)

-}

module CspCASL.Core_CspCASL (basicToCore) where

import CspCASL.AS_CspCASL
import CspCASL.AS_CspCASL_Process

basicToCore :: CspBasicSpec -> CspBasicSpec
basicToCore c = CspBasicSpec (channels c) (core_procs)
    where core_procs = map procEqToCore (processes c)
          procEqToCore (ProcEq pn p) = (ProcEq pn (procToCore p))

procToCore :: PROCESS -> PROCESS
procToCore proc = let p' = procToCore in case proc of
    -- First the core operators: we just need to recurse.
    Skip -> Skip
    Stop -> Skip
    PrefixProcess ev p -> PrefixProcess ev (p' p)
    ExternalPrefixProcess v es p -> ExternalPrefixProcess v es (p' p)
    InternalPrefixProcess v es p -> InternalPrefixProcess v es (p' p)
    Sequential p q -> Sequential (p' p) (p' q)
    ExternalChoice p q -> ExternalChoice (p' p) (p' q)
    InternalChoice p q -> InternalChoice (p' p) (p' q)
    GeneralisedParallel p es q -> GeneralisedParallel (p' p) es (p' q)
    Hiding p es -> Hiding (p' p) es
    RelationalRenaming p rn -> RelationalRenaming (p' p) rn
    NamedProcess pn evs -> NamedProcess pn evs
    ConditionalProcess f p q -> ConditionalProcess f (p' p) (p' q)
    -- Non-core, done.
    Interleaving p q -> GeneralisedParallel (p' p) EmptyEventSet (p' q)
    -- Non-core, not done yet.
    Div -> Div
    Run es -> Run es
    Chaos es -> Chaos es
    SynchronousParallel p q -> SynchronousParallel (p' p) (p' q)
    AlphabetisedParallel p esp esq q ->
        AlphabetisedParallel (p' p) esp esq (p' q)
