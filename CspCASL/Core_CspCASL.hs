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

import Common.Id

import CspCASL.AS_CspCASL
import CspCASL.AS_CspCASL_Process

basicToCore :: CspBasicSpec -> CspBasicSpec
basicToCore c = CspBasicSpec (channels c) (core_procs)
    where core_procs = map procEqToCore (proc_items c)
          procEqToCore (Proc_Eq pn p) = (Proc_Eq pn (procToCore p))
          procEqToCore x             = x

procToCore :: PROCESS -> PROCESS
procToCore proc = let p' = procToCore in case proc of
    -- First the core operators: we just need to recurse.
    (Skip r) -> (Skip r)
    (Stop r) -> (Stop r)
    (PrefixProcess ev p r) -> (PrefixProcess ev (p' p) r)
    (ExternalPrefixProcess v es p r) -> (ExternalPrefixProcess v es (p' p) r)
    (InternalPrefixProcess v es p r) -> (InternalPrefixProcess v es (p' p) r)
    (Sequential p q r) -> (Sequential (p' p) (p' q) r)
    (ExternalChoice p q r) -> (ExternalChoice (p' p) (p' q) r)
    (InternalChoice p q r) -> (InternalChoice (p' p) (p' q) r)
    (GeneralisedParallel p es q r) -> (GeneralisedParallel (p' p) es (p' q) r)
    (Hiding p es r) -> (Hiding (p' p) es r)
    (RelationalRenaming p rn r) -> (RelationalRenaming (p' p) rn r)
    (NamedProcess pn evs r) -> (NamedProcess pn evs r)
    (ConditionalProcess f p q r) -> (ConditionalProcess f (p' p) (p' q) r)
    -- Non-core, done.
    (Interleaving p q r) -> (GeneralisedParallel (p' p)
                             (EventSet [] nullRange) (p' q) r)
    -- Non-core, not done yet.
    (Div r) -> (Div r)
    (Run es r) -> (Run es r)
    (Chaos es r) -> (Chaos es r)
    (SynchronousParallel p q r) -> (SynchronousParallel (p' p) (p' q) r)
    (AlphabetisedParallel p esp esq q r) ->
        (AlphabetisedParallel (p' p) esp esq (p' q) r)
