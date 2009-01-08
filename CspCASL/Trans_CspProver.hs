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

import qualified CASL.AS_Basic_CASL as CASL_AS_Basic_CASL
import CASL.Fold as CASL_Fold
import qualified CASL.Sign as CASL_Sign

import Common.Id

import qualified Comorphisms.CFOL2IsabelleHOL as CFOL2IsabelleHOL

import CspCASL.AS_CspCASL_Process
import CspCASL.CspProver_Consts
import CspCASL.Trans_Consts

import Isabelle.IsaSign
import Isabelle.IsaConsts

transProcess :: CASL_Sign.Sign () () -> PROCESS -> Term
transProcess caslSign pr = case pr of
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
        cspProver_conditionalOp true (transProcess caslSign p)
                                     (transProcess caslSign q)
    -- precedence 2
    Hiding p es _ ->
        cspProver_hidingOp (transProcess caslSign p) (transEventSet es)
    RenamingProcess p r _ ->
        cspProver_renamingOp (transProcess caslSign p) (transRenaming r)
    -- precedence 3
    Sequential p q _ ->
        cspProver_sequenceOp (transProcess caslSign p) (transProcess caslSign q)
    PrefixProcess ev p _ ->
        cspProver_action_prefixOp (transEvent caslSign ev)
                                  (transProcess caslSign p)
    InternalPrefixProcess v s p _ ->
        cspProver_internal_prefix_choiceOp (transVar v)
                                           (transSort s)
                                           (transProcess caslSign p)
    ExternalPrefixProcess v s p _ ->
        cspProver_external_prefix_choiceOp (transVar v)
                                           (transSort s)
                                           (transProcess caslSign p)
    -- precedence 4
    InternalChoice p q _ ->
        cspProver_internal_choiceOp (transProcess caslSign p)
                                    (transProcess caslSign q)
    ExternalChoice p q _ ->
        cspProver_external_choiceOp (transProcess caslSign p)
                                    (transProcess caslSign q)
    -- precedence 5
    Interleaving p q _ ->
        cspProver_interleavingOp (transProcess caslSign p)
                                 (transProcess caslSign q)
    SynchronousParallel p q _ ->
        cspProver_synchronousOp (transProcess caslSign p)
                                (transProcess caslSign q)
    GeneralisedParallel p es q _ ->
        cspProver_general_parallelOp (transProcess caslSign p)
                                     (transEventSet es)
                                     (transProcess caslSign q)

    AlphabetisedParallel p les res q _ ->
        cspProver_alphabetised_parallelOp (transProcess caslSign p)
                                          (transEventSet les)
                                          (transEventSet res)
                                          (transProcess caslSign q)
    -- BUG not done right yet
    FQProcess p _ _ ->
        transProcess caslSign p

transEventSet :: EVENT_SET -> Term
transEventSet evs =
    let
        tranCommType ct = conDouble $ (tokStr ct) ++ barExtS
    in case evs of
         EventSet commTypes _ -> Set $ FixedSet $ map tranCommType commTypes

transEvent :: CASL_Sign.Sign () () -> EVENT -> Term
transEvent caslSign ev =
    case ev of
      TermEvent caslTerm _ -> transTerm_with_class caslSign caslTerm
      ChanSend _ _ _ -> conDouble "ChanSendNotYetDone"
      ChanNonDetSend _ _ _ _ -> conDouble "ChanNonDetSendNotYetDone"
      ChanRecv _ _ _ _ -> conDouble "ChanRecvNotYetDone"

transVar :: CASL_AS_Basic_CASL.VAR -> Term
transVar v = conDouble $ tokStr v

transSort :: CASL_AS_Basic_CASL.SORT -> Term
transSort sort = let sortBarString = convertSort2String sort ++ barExtS
                 in conDouble  sortBarString

transRenaming :: RENAMING -> Term
transRenaming _ = conDouble "not yet done"



-- BUG - I dont think these functions are correct
transTerm_with_class :: CASL_Sign.Sign () () -> CASL_AS_Basic_CASL.TERM () ->
                        Term
transTerm_with_class caslSign caslTerm =
    case caslTerm of
      -- if the term is just a variable then we just translate the
      -- variable to isabelle
      CASL_AS_Basic_CASL.Qual_var _ _ _ -> transCaslTerm caslSign caslTerm
      -- otherwise we add a classOp around it and translate the inside of
      -- it with the translator that adds a chooseOp
      _ -> classOp (transTerm_with_choose caslSign caslTerm)

transTerm_with_choose :: CASL_Sign.Sign () () -> CASL_AS_Basic_CASL.TERM () ->
                        Term
transTerm_with_choose caslSign caslTerm =
    case caslTerm of
      -- if the term is just a variable then we need to apply the choose
      -- function
      CASL_AS_Basic_CASL.Qual_var _ _ _ -> termAppl (conDouble "choose")
                                 (transCaslTerm caslSign caslTerm)
      -- otherwise we just translate it to Isabelle
      _ -> transCaslTerm caslSign caslTerm

-- | Translate a CASL Term to an Isabelle Term using the exact
--   translation as is done in the comorphism composition
--   CASL2PCFOL;defaultCASL2SubCFOL;CFOL2IsabelleHOL
transCaslTerm :: CASL_Sign.Sign () () -> CASL_AS_Basic_CASL.TERM () -> Term
transCaslTerm caslSign caslTerm =
    let tyToks = CFOL2IsabelleHOL.typeToks caslSign
        trForm = CFOL2IsabelleHOL.formTrCASL
        strs = CFOL2IsabelleHOL.getAssumpsToks caslSign
    in CASL_Fold.foldTerm (CFOL2IsabelleHOL.transRecord
                                           caslSign tyToks trForm strs)
     { foldQual_var = \ _ v s _ -> termAppl (conDouble $ "choose_" ++ show s)
                      $ mkFree $ CFOL2IsabelleHOL.transVar strs v }
     caslTerm


-- My own version of transRecord
-- transRecord_Term :: CASL.Sign.Sign f e -> Set.Set String -> FormulaTranslator f e
--             -> Set.Set String -> Record f Term Term
-- transRecord_Term sign tyToks tr toks = Record
--     { foldSimpleId = error "transRecord_Term: Simple_id"
--     , foldQual_var = \ _ v _ _ -> mkFree $ transVar toks v
--     , foldApplication = \ _ opsymb args _ ->
--           foldl termAppl (con $ transOP_SYMB sign tyToks opsymb) args
--     , foldSorted_term = \ _ t _ _ -> t -- no subsorting assumed
--     , foldCast = \ _ t _ _ -> t -- no subsorting assumed
--     , foldConditional = \ _  t1 phi t2 _ -> -- equal types assumed
--           If phi t1 t2 NotCont
--     , foldMixfix_qual_pred = error "transRecord_Term: Mixfix_qual_pred"
--     , foldMixfix_term = error "transRecord_Term: Mixfix_term"
--     , foldMixfix_token = error "transRecord_Term: Mixfix_token"
--     , foldMixfix_sorted_term = error "transRecord_Term: Mixfix_sorted_term"
--     , foldMixfix_cast = error "transRecord_Term: Mixfix_cast"
--     , foldMixfix_parenthesized = error "transRecord_Term: Mixfix_parenthesized"
--     , foldMixfix_bracketed = error "transRecord_Term: Mixfix_bracketed"
--     , foldMixfix_braced = error "transRecord_Term: Mixfix_braced"
--     }

-- transVar :: Set.Set String -> VAR -> String
-- transVar toks v = let
--     s = showIsaConstT (simpleIdToId v) baseSign
--     renVar t = if Set.member t toks then renVar $ "X_" ++ t else t
--     in renVar s

