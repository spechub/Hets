{- |
Module      :  $Header$
Description :  Provides transformations from Csp Processes to Isabelle terms
Copyright   :  (c) Liam O'Reilly and Markus Roggenbach,
                   Swansea University 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  csliam@swansea.ac.uk
Stability   :  provisional
Portability :  portable

Provides translations from Csp Processes to Isabelle terms

-}
module CspCASLProver.TransProcesses
    ( transProcess
    )where

import qualified CASL.AS_Basic_CASL as CASL_AS_Basic_CASL
import CASL.Fold as CASL_Fold
import qualified CASL.Sign as CASL_Sign

import Common.Id (tokStr)

import qualified Comorphisms.CFOL2IsabelleHOL as CFOL2IsabelleHOL

import CspCASL.AS_CspCASL_Process
import CspCASL.SignCSP

import CspCASLProver.Consts
import CspCASLProver.CspProverConsts

import Isabelle.IsaSign
import Isabelle.IsaConsts

-- | Translate a Process into CspProver (Isabelle). We need the data
--   part (CASL signature) for translating the translation of
--   terms. We also need the global variables so we can treat local
--   and global variables different.
transProcess :: CASL_Sign.Sign () () -> FQProcVarList -> PROCESS -> Term
transProcess caslSign globalVars pr = case pr of
    -- precedence 0
    Skip _ -> cspProver_skipOp
    Stop _ -> cspProver_stopOp
    Div  _ -> cspProver_divOp
    Run es _ -> App (cspProver_runOp) (transEventSet es) NotCont
    Chaos es _ -> App (cspProver_chaosOp) (transEventSet es) NotCont
    NamedProcess pn fqParams _ ->
        let -- Make a process name term
            pnTerm = conDouble $ convertProcessName2String pn
            -- Translate an argument(a term) as normal but make sure
            -- we land in the bar types and not in the alphabet
            transParam t = transTerm False globalVars caslSign t
            -- Create a list of translated parameters
            paramTerms = map transParam fqParams
        in if (null fqParams)
        -- If there are no parameters we just get the process name term
        then cspProver_NamedProcOp $ pnTerm
        -- Otherwise we get the process name term applied to the parameters
        else cspProver_NamedProcOp $ foldl termAppl pnTerm paramTerms
    -- precedence 1
    ConditionalProcess _ p q _ ->
        cspProver_conditionalOp true (transProcess caslSign globalVars p)
                                     (transProcess caslSign globalVars q)
    -- precedence 2
    Hiding p es _ ->
        cspProver_hidingOp (transProcess caslSign globalVars p) (transEventSet es)
    RenamingProcess p r _ ->
        cspProver_renamingOp (transProcess caslSign globalVars p) (transRenaming r)
    -- precedence 3
    Sequential p q _ ->
        cspProver_sequenceOp (transProcess caslSign globalVars p)
                                 (transProcess caslSign globalVars q)
    PrefixProcess ev p _ ->
        -- All prefix events are dealt with inside the translation of events.
        transEvent caslSign globalVars ev p
    -- precedence 4
    InternalChoice p q _ ->
        cspProver_internal_choiceOp (transProcess caslSign globalVars p)
                                    (transProcess caslSign globalVars q)
    ExternalChoice p q _ ->
        cspProver_external_choiceOp (transProcess caslSign globalVars p)
                                    (transProcess caslSign globalVars q)
    -- precedence 5
    Interleaving p q _ ->
        cspProver_interleavingOp (transProcess caslSign globalVars p)
                                 (transProcess caslSign globalVars q)
    SynchronousParallel p q _ ->
        cspProver_synchronousOp (transProcess caslSign globalVars p)
                                (transProcess caslSign globalVars q)
    GeneralisedParallel p es q _ ->
        cspProver_general_parallelOp (transProcess caslSign globalVars p)
                                     (transEventSet es)
                                     (transProcess caslSign globalVars q)

    AlphabetisedParallel p les res q _ ->
        cspProver_alphabetised_parallelOp (transProcess caslSign globalVars p)
                                          (transEventSet les)
                                          (transEventSet res)
                                          (transProcess caslSign globalVars q)
        -- Just forget the fully qualified data i.e. the constituent
        -- communication alphabet. Translate as normal.
    FQProcess p _ _ ->
        transProcess caslSign globalVars p

transEventSet :: EVENT_SET -> Term
transEventSet evs =
    let
        -- tran_COMM_TYPE ct = conDouble $ (tokStr ct) ++ barExtS
        -- tran_commType ct = conDouble $ (tokStr ct) ++ barExtS
    in case evs of
         EventSet _ _ -> conDouble "EventSetNotYetDone"
           -- Set $ FixedSet $ map tran_COMM_TYPE commTypes
         FQEventSet _ _ -> conDouble "FQEventSetNotYetDone"
           -- Set $ FixedSet $ map tranCommType commTypes

-- | Translate a process event into CspProver (Isabelle). We need to
--   know the data pat (CASL signature) inorder to use the same
--   translation for CASL terms as the data encoding into Isabelle
--   did. We also need the global variables so we can treat local and
--   global variables different.
transEvent :: CASL_Sign.Sign () () -> FQProcVarList -> EVENT -> PROCESS -> Term
transEvent caslSign globalVars event p =
    case event of
      -- To use the fully qualified data we need to know what the underlying
      -- type of the process is
      FQEvent ev _ fqTerm _ ->
          case ev of
            TermEvent _ _ ->
                -- Translate the term and make sure we do land in the
                -- alphabet and not in the bar types
                cspProver_action_prefixOp (transTerm True globalVars caslSign fqTerm)
                                              (transProcess caslSign globalVars p)
            InternalPrefixChoice v s _ ->
                -- Use the nonfully qualified data instead of the fully
                -- qualified data as it is easier in this case as the variable
                -- is not really a variable of that sort. Here the variable and
                -- sort are seperate operands of the CSPProver operator.
                cspProver_internal_prefix_choiceOp
                (transVar v) (transSort s) (transProcess caslSign globalVars p)
            ExternalPrefixChoice v s _ ->
                -- Use the nonfully qualified data instead of the fully
                -- qualified data as it is easier in this case as the variable
                -- is not really a variable of that sort. Here the variable and
                -- sort are seperate operands of the CSPProver operator.
                cspProver_external_prefix_choiceOp
                  (transVar v) (transSort s) (transProcess caslSign globalVars p)
            ChanSend _ _ _ -> conDouble "ChanSendNotYetDone"
            ChanNonDetSend _ _ _ _ -> conDouble "ChanNonDetSendNotYetDone"
            ChanRecv _ _ _ _ -> conDouble "ChanRecvNotYetDone"

-- | Translate a variable into CspProver (Isabelle). Notice
--   that this does not work on fully qualified CASL variables (TERMs)
--   but instead on VAR.
transVar :: CASL_AS_Basic_CASL.VAR -> Term
transVar v = conDouble $ tokStr v

-- | Translate a sort into CspProver (Isabelle). The result will be
--   the corresponding bar type for a given sort.
transSort :: CASL_AS_Basic_CASL.SORT -> Term
transSort sort = conDouble $ mkSortBarString sort

transRenaming :: RENAMING -> Term
transRenaming _ = conDouble "RenamingNotDoneYet"

-- | Translate a process term in to Isabelle HOL. The first parameter
--   decides if we should land in the alphabet or in a bar type. Both
--   of these are related by Abstraction and Representation fucntions
--   in Isabelle. The second parameter is he global variables of the
--   process. The third parameter is the data part (CASL signature)
--   for translating the translation of terms.
transTerm :: Bool -> FQProcVarList -> CASL_Sign.Sign () () -> CASL_AS_Basic_CASL.TERM () -> Term
transTerm toAlphabet globalVars caslSign caslTerm =
    let strs = CFOL2IsabelleHOL.getAssumpsToks caslSign in
    case caslTerm of
      -- if the term is just a variable then we need to check if its
      -- global and if we land in the alphabet or not. Each case has
      -- different behaviour.
      CASL_AS_Basic_CASL.Qual_var v s r ->
          let v' = mkFree $ CFOL2IsabelleHOL.transVar strs v
          in
            -- Check if the variable is a global variabe
            if ((CASL_AS_Basic_CASL.Qual_var v s r) `elem` globalVars)
            then
                -- Its a global Variable
                -- Check if we are to land in the alphabet or now
                if (toAlphabet)
                then
                    -- Land in the Alphabet
                    (mkSortBarRepOp s) v'
                else
                    -- Land in the Bar Types
                    v' -- Its already in the Bar Ype as its global
            else
                -- Its a local Variable
                -- Check if we are to land in the alphabet or now
                if (toAlphabet)
                then
                    -- Land in the Alphabet
                    v' -- Its already in the alphabet as its local
                else
                    -- Land in the Bar Types
                    (mkSortBarAbsOp s) v'

      -- otherwise (not a variable) we add a classOp and constructor
      -- around it and translate the arguments with the transCaslTermWithoutWrap
      -- translator that adds a chooseOp, representation and
      -- abstraction fucntiosn where needed.
      _ -> let sort = CASL_Sign.sortOfTerm caslTerm
               -- Make a haskell function that will apply the constructor around
               -- an Isabelle term.
               constructor = mkPreAlphabetConstructorOp sort
               -- Build the translation of the term wrapped in the constructor
               -- wrapped in the class operation.
               isaCaslTerm = classOp $ constructor $
                             transCaslTermWithoutWrap caslSign
                                                      globalVars caslTerm
           in if (toAlphabet)
              then isaCaslTerm
              else (mkSortBarAbsOp sort) isaCaslTerm

-- | Translate a CASL Term to an Isabelle Term using the exact
--   translation as is done in the comorphism composition
--   CASL2PCFOL;defaultCASL2SubCFOL;CFOL2IsabelleHOL. With one
--   exception, If we are translating a variable then we must first
--   add the correct choose function around it to change it from an
--   equivalence class to value of the underlying sort. Also if we are
--   translating a variable and the the variable is a global process
--   variable then we must first apply the representation fucntion to
--   the variable. This function will always return a term that is in
--   the basic Sorts. i.e. to make it part of the alphabet it will
--   need to be wrapped up in a class operation with the necessary
--   constructor.
transCaslTermWithoutWrap :: CASL_Sign.Sign () () -> FQProcVarList ->
                            CASL_AS_Basic_CASL.TERM () -> Term
transCaslTermWithoutWrap caslSign globalVars caslTerm =
    let tyToks = CFOL2IsabelleHOL.typeToks caslSign
        trForm = CFOL2IsabelleHOL.formTrCASL
        strs = CFOL2IsabelleHOL.getAssumpsToks caslSign
    in CASL_Fold.foldTerm (CFOL2IsabelleHOL.transRecord
                                           caslSign tyToks trForm strs)
     -- We use the existing record for translation but change its
     -- function in the case of a qualified variable. If we have a
     -- variable then translate the variable but wrap it in the
     -- correct choose function for it's sort.
     { foldQual_var = \ _ v s r ->
       let v' = mkFree $ CFOL2IsabelleHOL.transVar strs v
       in -- If the variable is a global variable then add the
          -- representation function before the choose function.
          if ((CASL_AS_Basic_CASL.Qual_var v s r) `elem` globalVars)
          then
              -- Global variable
              mkChooseFunOp s $ mkSortBarRepOp s $ v'
          else
              -- Local variable
              mkChooseFunOp s $ v'
     }
     caslTerm
