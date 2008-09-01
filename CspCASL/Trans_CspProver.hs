{- |
Module      :  $Header$
Description :  Provides transformations from Csp Processes to Isabelle terms
Copyright   :  (c) Andy Gimblett, Liam O'Reilly and Markus Roggenbach,
                   Swansea University 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  csliam@swansea.ac.uk
Stability   :  provisional
Portability :  portable

Provides transformations from Csp Processes to Isabelle terms

-}
module CspCASL.Trans_CspProver where

import CASL.AS_Basic_CASL (SORT, VAR)

import Common.Id

import CspCASL.AS_CspCASL_Process
import CspCASL.CspProver_Consts
import CspCASL.Trans_Consts

import Isabelle.IsaSign
import Isabelle.IsaConsts

transProcess :: PROCESS -> Term
transProcess pr = case pr of
    -- precedence 0
    Skip _ -> cspProver_skipOp
    Stop _ -> cspProver_stopOp
    Div  _ -> cspProver_divOp
    Run es _ -> App (cspProver_runOp) (transEventSet es) NotCont
    Chaos es _ -> App (cspProver_chaosOp) (transEventSet es) NotCont
    NamedProcess pn ts _ ->
        let pnTerm = conDouble $ show pn
        in if (null ts)
        then pnTerm
        else App pnTerm (conDouble $ show ts) NotCont
    -- precedence 1
    ConditionalProcess _ p q _ ->
        cspProver_conditionalOp true (transProcess p) (transProcess q)
    -- precedence 2
    Hiding p es _ ->
        cspProver_hidingOp (transProcess p) (transEventSet es)
    RenamingProcess p r _ ->
        cspProver_renamingOp (transProcess p) (transRenaming r)
    -- precedence 3
    Sequential p q _ ->
        cspProver_sequenceOp (transProcess p) (transProcess q)
    PrefixProcess ev p _ ->
        cspProver_action_prefixOp (transEvent ev) (transProcess p)
    InternalPrefixProcess v s p _ ->
        cspProver_internal_prefix_choiceOp (transVar v)
                                           (transSort s)
                                           (transProcess p)
    ExternalPrefixProcess v s p _ ->
        cspProver_external_prefix_choiceOp (transVar v)
                                           (transSort s)
                                           (transProcess p)
    -- precedence 4
    InternalChoice p q _ ->
        cspProver_internal_choiceOp (transProcess p) (transProcess q)
    ExternalChoice p q _ ->
        cspProver_external_choiceOp (transProcess p) (transProcess q)
    -- precedence 5
    Interleaving p q _ ->
        cspProver_interleavingOp (transProcess p) (transProcess q)
    SynchronousParallel p q _ ->
        cspProver_synchronousOp (transProcess p) (transProcess q)
    GeneralisedParallel p es q _ ->
        cspProver_general_parallelOp (transProcess p)
                                     (transEventSet es)
                                     (transProcess q)

    AlphabetisedParallel p les res q _ ->
        cspProver_alphabetised_parallelOp (transProcess p)
                                          (transEventSet les)
                                          (transEventSet res)
                                          (transProcess q)

transEventSet :: EVENT_SET -> Term
transEventSet evs =
    let
        tranCommType ct = conDouble $ (tokStr ct) ++ barExtS
    in case evs of
         EventSet commTypes _ -> Set $ FixedSet $ map tranCommType commTypes

transEvent :: EVENT -> Term
transEvent ev =
    case ev of
      TermEvent caslTerm _ -> conDouble "not yet done"
      ChanSend _ _ _ -> conDouble "not yet done"
      ChanNonDetSend _ _ _ _ -> conDouble "not yet done"
      ChanRecv _ _ _ _ -> conDouble "not yet done"

transVar :: VAR -> Term
transVar v = conDouble $ tokStr v

transSort :: SORT -> Term
transSort sort = let sortBarString = convertSort2String sort ++ barExtS
                 in conDouble  sortBarString

transRenaming :: RENAMING -> Term
transRenaming _ = conDouble "not yet done"
