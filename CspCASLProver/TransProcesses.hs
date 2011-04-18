{- |
Module      :  $Header$
Description :  Provides transformations from Csp Processes to Isabelle terms
Copyright   :  (c) Liam O'Reilly and Markus Roggenbach,
                   Swansea University 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  csliam@swansea.ac.uk
Stability   :  provisional
Portability :  portable

Provides translations from Csp Processes to Isabelle terms

-}
module CspCASLProver.TransProcesses
    ( transProcess
    , VarSource (..)
    ) where

import qualified CASL.AS_Basic_CASL as CASL_AS_Basic_CASL
import CASL.Fold as CASL_Fold
import qualified CASL.Sign as CASL_Sign
import qualified CASL.Simplify as CASL_Simplify

import Common.Id (tokStr)
import Common.Result (propagateErrors)
import Common.Utils (number)

import qualified Comorphisms.CASL2PCFOL as CASL2PCFOL
import qualified Comorphisms.CASL2SubCFOL as CASL2SubCFOL
import qualified Comorphisms.CFOL2IsabelleHOL as CFOL2IsabelleHOL

import CspCASL.AS_CspCASL_Process
import CspCASL.SignCSP (CspCASLSign, ccSig2CASLSign)

import CspCASL.StatAnaCSP (getDeclaredChanSort)

import CspCASLProver.Consts
import CspCASLProver.CspProverConsts

import qualified Data.Set as Set
import qualified Data.Map as Map

import Isabelle.IsaSign
import Isabelle.IsaConsts

-- | The origin of a variable
data VarSource
    -- | indicates that the variable originated from a prefix choice operator.
    = PrefixChoice
    -- | indicates that the variable originated from a channel nondeterministic
    -- send or channel receive where the sort is the declared sort of the
    -- channel.
    | ChanSendOrRec CASL_AS_Basic_CASL.SORT
    -- | indicates that the variable originated from global parameter to the
    -- process.
    | GlobalParameter

-- | The target of the sort translation
data SortTarget
    -- | Indicates the translated sort will be used as a normal communication
    -- e.g., as a prefix choice or event set.
    = NormalComm
    -- | Indicates that the sort will be used as a communication set with a
    -- channel of certain declared sort.
    | ChanComm CASL_AS_Basic_CASL.SORT

-- | The taraget of the term translation
data TermTarget
    -- | Indicates the term will be used in the term prefix operator
    = TermPrefix
    -- | Indicates that the term will be used either as a parameter (where sort
    -- | is declared sort of the parameter) or as a channel communication (where
    -- | the sort is the declared sort of the channel).
    | ChanSendOrParam CASL_AS_Basic_CASL.SORT

-- | Variable source map, which maps variables to the source of the variable.
type VSM = Map.Map CASL_AS_Basic_CASL.VAR VarSource

-- | Translate a Process into CspProver (Isabelle). We need the data part (CASL
-- signature) for translating the translation of terms. We also need the
-- global variables so we can treat local and global variables different. We
-- need the PCFOL and CFOL signature of the data part after translation to
-- PCFOL and CFOL to pass along to the term and formula translations.
transProcess :: CspCASLSign -> CASL_Sign.Sign () () ->
                CASL_Sign.Sign () () -> VSM -> PROCESS -> Term
transProcess ccSign pcfolSign cfolSign vsm pr =
    let -- Make translations with all the signatures filled in
        transFormula' = transFormula pcfolSign cfolSign
        transProcess' =
            transProcess ccSign pcfolSign cfolSign
        -- cspSign = ccSig2CspSign ccSign
        caslSign = ccSig2CASLSign ccSign
        -- getProcParamSort procName index =
        --     let procMap = procSet cspSign
        --         paramSortList = case Map.lookup procName procMap of
        --                      Nothing -> error "CspCASLProver.TransProcesses.transProcess: Process name not found in process map."
        --                      Just pp-> error "NYI: CspCASLProver.TransProcesses.transProcess: Not updated for new signatures yet" -- case pp of ProcProfile sorts _ -> sorts
        --     in paramSortList !! index
    in case pr of
         -- precedence 0
         Skip _ -> cspProver_skipOp
         Stop _ -> cspProver_stopOp
         Div _ -> cspProver_divOp
         -- Run -> App (cspProver_runOp) (head (transEventSet es)) NotCont
         Run _ _ -> conDouble "RunNotSupportedYet"
         -- Chaos -> App (cspProver_chaosOp) (head (transEventSet es)) NotCont
         Chaos _ _ -> conDouble "ChaosNotSupportedYet"
         NamedProcess fqpn fqParams _ ->
             let -- Make a process name term
                 pnTerm = conDouble $ convertFQProcessName2String fqpn
                 -- Translate an argument(a term), t is the sort of the declared
                 -- parameter (the sort of the variable may be a subsort of the
                 -- declared sort, so we must use the declared sort).
                 -- transParam (term, declaredSortIndex) =
                 transParam (term, _) =
                     let termTar = ChanSendOrParam $
                                   error "NYI: CspCASLProver.TransProcesses.transProcess: Not updated for new signatures yet" -- getProcParamSort pn (declaredSortIndex - 1)
                     in transCASLTerm caslSign pcfolSign cfolSign
                        vsm termTar term
                 -- Create a list of translated parameters, we number the
                 -- parameters from one
                 paramTerms = map transParam $ number fqParams
             in if null fqParams
                -- If there are no parameters we just get the process name term
                then cspProver_NamedProcOp pnTerm
                -- Otherwise we get the process name term applied to the
                -- parameters
                else cspProver_NamedProcOp $ foldl termAppl pnTerm paramTerms
         -- precedence 1
         ConditionalProcess fqFormula p q _ ->
             cspProver_conditionalOp (transFormula' vsm fqFormula)
                                         (transProcess' vsm p)
                                         (transProcess' vsm q)
         -- precedence 2
         Hiding _ _ _ -> conDouble "HidingNotSupportedYet"
             -- cspProver_hidingOp (transProcess' p) (union (transEventSet es))
         RenamingProcess _ _ _ -> conDouble "RenamingNotSupportedYet"
             -- cspProver_renamingOp (transProcess' p) (transRenaming re)
         -- precedence 3
         Sequential p q _ ->
             cspProver_sequenceOp (transProcess' vsm p) (transProcess' vsm q)
         PrefixProcess ev p _ ->
         -- All prefix events are dealt with inside the translation of events.
             transEvent ccSign pcfolSign cfolSign vsm ev p
         -- precedence 4
         InternalChoice p q _ ->
             cspProver_internal_choiceOp (transProcess' vsm p)
                                             (transProcess' vsm q)
         ExternalChoice p q _ ->
             cspProver_external_choiceOp (transProcess' vsm p)
                                             (transProcess' vsm q)
         -- precedence 5
         Interleaving p q _ ->
             cspProver_interleavingOp (transProcess' vsm p)
                                          (transProcess' vsm q)
         SynchronousParallel p q _ ->
             cspProver_synchronousOp (transProcess' vsm p)
                                         (transProcess' vsm q)
         GeneralisedParallel p es q _ ->
             cspProver_general_parallelOp (transProcess' vsm p)
                                              (transEventSet es)
                                              (transProcess' vsm q)

         AlphabetisedParallel p les res q _ ->
             cspProver_alphabetised_parallelOp (transProcess' vsm p)
                                                   (transEventSet les)
                                                   (transEventSet res)
                                                   (transProcess' vsm q)
         -- Just forget the fully qualified data i.e. the constituent
         -- communication alphabet. Translate as normal.
         FQProcess p _ _ ->
             transProcess' vsm p

-- | Translate a fully qualified EventSet into a list Isabelle term.
transEventSet :: EVENT_SET -> Term
transEventSet evs =
    case evs of
      EventSet _ _ ->
          error $ "CspCASLProver.TransProcesses.transEventSet: "
            ++ "Expected a FQEventSet not a non-FQEventSet"
      FQEventSet comms _ ->
          -- This list will not be empty otherwise, if it was empty the static
          -- analysis would have failed.
          foldr1 binUnion (map transCommType comms)

-- | Translate a fully qualified CommType into an Isabelle term.
transCommType :: CommType -> Term
transCommType comm =
    case comm of
      CommTypeSort sort -> transSort NormalComm sort
      CommTypeChan typedChanName ->
          case typedChanName of
            TypedChanName cn _ -> rangeOp (conDouble $ convertChannelString cn)

-- | Translate a process event into CspProver (Isabelle). We need to know the
-- data part (CASL signature) in order to use the same translation for CASL
-- terms as the data encoding into Isabelle did. We need the Csp signature for
-- getting the declared channel sorts. We need the PCFOL and CFOL signature of
-- the data part after translation to PCFOL and CFOL to pass along to the term
-- and formula translations. We need the vsm to pass it on to the term
-- translation.
transEvent :: CspCASLSign -> CASL_Sign.Sign () () ->
              CASL_Sign.Sign () () -> VSM ->
              EVENT -> PROCESS -> Term
transEvent ccSign pcfolSign cfolSign vsm event p =
    let -- Make translation with all the signatures filled in
        transProcess' = transProcess ccSign pcfolSign cfolSign
        caslSign = ccSig2CASLSign ccSign
        transCASLTerm' = transCASLTerm caslSign pcfolSign cfolSign
    in case event of
      -- To use the fully qualified data we need to know what the underlying
      -- type of the process is
      FQEvent ev mfqc fqTerm _ ->
          case ev of
            TermEvent _ _ ->
                -- Translate the term for use in the term prefix operator
                cspProver_action_prefixOp (transCASLTerm' vsm TermPrefix fqTerm)
                (transProcess' vsm p)
            InternalPrefixChoice v s _ ->
                -- Use the non fully qualified data instead of the fully
                -- qualified data as it is easier in this case as the variable
                -- is not really a variable of that sort. Here the variable and
                -- sort are separate operands of the CSPProver operator.
                cspProver_internal_prefix_choiceOp
                (transVar v) (transSort NormalComm s)
                                 (transProcess'
                                  (Map.insert v PrefixChoice vsm) p)
            ExternalPrefixChoice v s _ ->
                -- Use the non fully qualified data instead of the fully
                -- qualified data as it is easier in this case as the variable
                -- is not really a variable of that sort. Here the variable and
                -- sort are separate operands of the CSPProver operator.
                cspProver_external_prefix_choiceOp
                  (transVar v) (transSort NormalComm s)
                                   (transProcess'
                                    (Map.insert v PrefixChoice vsm) p)
            ChanSend _ _ _ ->
                -- We do not use the non fully qualified term or channel name.
                -- Instead we use the fully qualified term (fqTerm) and the
                -- fully qualified channel (mfqc)
                case mfqc of
                  Nothing -> error "CspCASLProver.TransProcesses.transEvent: Missing fully qualified channel data"
                  Just (chanName, chanSort) ->
                      -- CspProver's channel send Op
                      cspProver_chan_sendOp
                      -- Name of channel
                      (transChanName chanName)
                      -- Term to send
                      (transCASLTerm' vsm (ChanSendOrParam chanSort) fqTerm)
                      -- The translated version of the rest of the process
                      (transProcess' vsm p)

            ChanNonDetSend _ var varSort _ ->
                -- We do not use the fully qualified variable (fqTerm) instead
                -- we use the non fully qualified variable (var, varSort).
                case mfqc of
                  Nothing -> error "CspCASLProver.TransProcesses.transEvent: Missing fully qualified channel data"
                             -- Notice we do not use the derived channel's
                             -- sort(second of Just) as this can be a sub type
                             -- of the declared channel sort, which is what we
                             -- need.
                  Just (chanName, _) ->
                      let declaredChanSort = propagateErrors
                            "CspCASLProver.TransProcesses.transEvent1"
                            $ getDeclaredChanSort mfqc ccSign
                      -- CspProvers non-deterministic channel send Op
                      in cspProver_chan_nondeterministic_sendOp
                      -- The channel name
                      (transChanName chanName)
                      -- The translated variable
                      (transVar var)
                      -- The translate sort (channel version) of the set to
                      -- receive from. Note that the sort in the mfqc is the
                      -- sort of the variable as specified, we want here the
                      -- declaration sort of the channel.
                      (transSort (ChanComm declaredChanSort) varSort)
                      -- The translated version of the rest of the process
                      (transProcess' (Map.insert var
                                      (ChanSendOrRec declaredChanSort) vsm) p)

            ChanRecv _ var varSort _ ->
                -- We do not use the fully qualified variable (fqTerm) instead
                -- we use the non fully qualified variable (var, varSort).
                case mfqc of
                  Nothing -> error "CspCASLProver.TransProcesses.transEvent: Missing fully qualified channel data"
                  -- Notice we do not use the derived channel's sort(second of
                  -- Just) as this can be a sub type of the declared channel
                  -- sort, which is what we need.
                  Just (chanName, _) ->
                      let declaredChanSort = propagateErrors
                            "CspCASLProver.TransProcesses.transEvent2"
                            $ getDeclaredChanSort mfqc ccSign
                      -- CspProvers channel receive Op
                      in cspProver_chan_recOp
                      -- The channel name
                      (transChanName chanName)
                      -- The translated variable
                      (transVar var)
                      -- The translate sort (channel version) of the set to
                      -- receive from. Note that the sort in the mfqc is the
                      -- sort of the variable as specified, we want here the
                      -- declaration sort of the channel.
                      (transSort (ChanComm declaredChanSort) varSort)
                      -- The translated version of the rest of the process
                      (transProcess' (Map.insert var
                                      (ChanSendOrRec declaredChanSort) vsm) p)

            FQEvent _ _ _ _ ->
              error $ "CspCASLProver.TransProcesses.transEvent: "
                ++ "A FQEvent should not contain a non-FQEvent"
      _ -> error $ "CspCASLProver.TransProcesses.transEvent: "
             ++ "Expected a FQEvent not a non-FQEvent"

-- | Translate a variable into CspProver (Isabelle). Notice
-- that this does not work on fully qualified CASL variables (TERMs)
-- but instead on VAR.
transVar :: CASL_AS_Basic_CASL.VAR -> Term
transVar v = conDouble $ tokStr v

-- | Translate a sort into CspProver (Isabelle) depending on the target of the
-- sort.
transSort :: SortTarget -> CASL_AS_Basic_CASL.SORT -> Term
transSort target s =
    let sBar = conDouble $ mkSortBarString s
    in case target of
         NormalComm -> binImageOp (conDouble flatS) sBar
         ChanComm t -> binImageOp
                       (conDouble $ mkSortBarAbsString t) sBar

-- | Translated the channel name to Isabelle code.
transChanName :: CHANNEL_NAME -> Term
transChanName chanName =
    conDouble $ convertChannelString chanName

-- transRenaming :: RENAMING -> Term
-- transRenaming _ = conDouble "RenamingNotDoneYet"

-- -----------------------------------------------------------------------
-- Functions the translations of CASL terms and formulae               --
-- -----------------------------------------------------------------------

-- | Produce a record that is used to translate CASL terms and formulae to
-- Isabelle Terms. This record is the same as the CFOL2IsabelleHOL.transRecord
-- but deals with variables by applying a case on the origin of the
-- variable. The Isabelle terms produced when this record is used are always
-- of basic types i.e., can be used as parameters for function in the data
-- encoding.
cspCaslTransRecord :: CASL_Sign.Sign f e -> Set.Set String ->
                      CFOL2IsabelleHOL.FormulaTranslator f e ->
                      Set.Set String -> VSM -> Record f Term Term
cspCaslTransRecord caslSign tyToks trForm strs vsm =
     -- We use the existing record for translation but change its
     -- function in the case of a qualified variable. If we have a
     -- variable then we must make a translate the variable but wrap it in the
     -- correct choose function for it's sort.
    (CFOL2IsabelleHOL.transRecord caslSign tyToks trForm strs)
    { foldQual_var = \ _ v s _ ->
      let v' = mkFree $ CFOL2IsabelleHOL.transVar strs v
      in case (Map.lookup v vsm) of
           Nothing ->
               error $ "CspCASLProver.TransProcesses.cspCaslTransRecord: Variable not found in vsm:" ++ show v
           Just varSource ->
               case varSource of
                 PrefixChoice -> mkChooseFunOp s $ projFlatOp v'
                 ChanSendOrRec declaredChanSort ->
                     mkChooseFunOp s $ mkSortBarRepOp declaredChanSort v'
                 GlobalParameter -> mkChooseFunOp s $ mkSortBarRepOp s v'
    }

-- | Translate a CASL term into an Isabelle term. The result of this function
-- depends on the term target. a target of TermPrefix indicates we must land
-- in the alphabet and have a flat constructor wrapped around the
-- translation. A ChanSendOrParam indicates that the translated term will be
-- used in a channel send operator or as a parameter to a named process. The
-- translation also changes depending on the source of the variables used.
transCASLTerm :: CASL_Sign.Sign () () -> CASL_Sign.Sign () () ->
                 CASL_Sign.Sign () () -> VSM -> TermTarget ->
                 CASL_AS_Basic_CASL.TERM () -> Term
transCASLTerm caslSign pcfolSign cfolSign vsm termTarget caslTerm =
    let strs = CFOL2IsabelleHOL.getAssumpsToks caslSign
    -- We make a case on the type of term, then on the term target, then if we
    -- have a variable we make a case on the source of the variable
    in case caslTerm of
         -- Variable
         CASL_AS_Basic_CASL.Qual_var v s _ ->
             let v' = mkFree $ CFOL2IsabelleHOL.transVar strs v
             in case termTarget of
               TermPrefix ->
                   case (Map.lookup v vsm) of
                     Nothing -> error $ "CspCASLProver.TransProcesses.transTerm: Variable not found in vsm:" ++ show v
                     Just varSource ->
                         case varSource of
                           PrefixChoice -> v' -- the variable is already ok
                           ChanSendOrRec declaredChanSort ->
                               flatOp $ mkSortBarRepOp declaredChanSort v'
                           GlobalParameter -> flatOp $ mkSortBarRepOp s v'
               ChanSendOrParam t ->
                   case Map.lookup v vsm of
                     Nothing -> error $ "CspCASLProver.TransProcesses.transTerm: Variable not found in vsm:" ++ show v
                     Just varSource ->
                         case varSource of
                           PrefixChoice ->
                               mkSortBarAbsOp t $ projFlatOp v'
                           ChanSendOrRec declaredChanSort ->
                               if declaredChanSort == t
                               then v'
                               else mkSortBarAbsOp t $
                                    mkSortBarRepOp declaredChanSort v'
                           GlobalParameter ->
                               if s == t
                               then v'
                               else mkSortBarAbsOp t $
                                    mkSortBarRepOp s v'
         -- Other (not a variable)
         _ -> let sort = CASL_Sign.sortOfTerm caslTerm
                  -- Make a Haskell function that will apply the constructor
                  -- around an Isabelle term.
                  constructor = mkPreAlphabetConstructorOp sort
                  -- Build the translation of the term wrapped in the
                  -- constructor wrapped in the class operation.
                  isaCaslTerm = classOp $ constructor $
                                transCaslTermComputation pcfolSign cfolSign
                                                         vsm caslTerm
              in case termTarget of
                   TermPrefix -> flatOp isaCaslTerm
                   ChanSendOrParam t -> mkSortBarAbsOp t isaCaslTerm

-- | Translate a CASL Term to an Isabelle Term using the exact translation as is
-- done in the comorphism composition
-- CASL2PCFOL;defaultCASL2SubCFOL;CFOL2IsabelleHOL with out customised
-- variable translation (see cspCaslTransRecord for where that customisation
-- is define). The resulting Isabelle term of this function will be of the
-- underlying sort types, thus can be used as parameters of CASL functions in
-- the data part. We need the PCFOL and CFOL signature of the data part after
-- translation to CFOL to translate the formula.
transCaslTermComputation :: CASL_Sign.Sign () () -> CASL_Sign.Sign () () ->
                            VSM -> CASL_AS_Basic_CASL.TERM () -> Term
transCaslTermComputation pcfolSign cfolSign vsm term =
    let -- Function to remove subsorting - from comorphism CASL2PCFOL
        rmSub = CASL2PCFOL.t2Term
        -- Remove subsorting from the term
        termNoSub = rmSub term
        -- Function to remove partiality - from comorphism CASL2SubPCFOL
        -- This needs to match the translation CASL2SubCFOL.defaultCASL2SubCFOL
        b = True -- We want unique bottom elements per sort
        -- Calculate the bottom sorts for the term and signature
        fbsrts = CASL2SubCFOL.botTermSorts termNoSub
        bsrts = CASL2SubCFOL.sortsWithBottom CASL2SubCFOL.FormulaDependent
                pcfolSign fbsrts
        rmPartial = CASL_Simplify.simplifyTerm id .
                    CASL2SubCFOL.codeTerm b bsrts
        -- Function to translate to Isabelle - from comorphism CFOL2IsabelleHOL
        -- We need the CFOL signature to translate the terms properly
        tyToks = CFOL2IsabelleHOL.typeToks cfolSign
        trForm = CFOL2IsabelleHOL.formTrCASL
        strs = CFOL2IsabelleHOL.getAssumpsToks cfolSign
        toIsabelle = foldTerm $ cspCaslTransRecord cfolSign
                     tyToks trForm strs vsm
        -- CFOL2IsabelleHOL.transFORMULA cfolSign tyToks trForm strs
    in toIsabelle $ rmPartial termNoSub

-- | Translate a fully qualified CASL formula into an Isabelle Term using the
-- exact translation as is done in the comorphism composition
-- CASL2PCFOL;defaultCASL2SubCFOL;CFOL2IsabelleHOL except translate CASL terms
-- using the CASL term translation for computation, where the terms will be
-- translated such that they are of the underlying sort types and thus can be
-- used as operands to the formula operators.
transFormula :: CASL_Sign.Sign () () -> CASL_Sign.Sign () () -> VSM ->
                CASL_AS_Basic_CASL.FORMULA () -> Term
transFormula pcfolSign cfolSign vsm formula =
    let -- Function to remove subsorting - from comorphism CAS2PCFOL
        rmSub = CASL2PCFOL.f2Formula
        -- Remove subsorting from the formula
        formulaNoSub = rmSub formula
        -- Function to remove partiality - from comorphism CAS2SubPCFOL
        -- This needs to match the translation CASL2SubCFOL.defaultCASL2SubCFOL
        b = True -- We want unique bottom elements per sort
        -- Calculate the bottom sorts for the formula and signature
        fbsrts = CASL2SubCFOL.botFormulaSorts formulaNoSub
        bsrts = CASL2SubCFOL.sortsWithBottom CASL2SubCFOL.FormulaDependent
                pcfolSign fbsrts
        rmPartial = CASL_Simplify.simplifyFormula id .
                    CASL2SubCFOL.codeFormula b bsrts
        -- Function to tranalate to Isabelle - from comorphism CFOL2IsabelleHOL
        -- We need the CFOL signature to translate the formula properly
        tyToks = CFOL2IsabelleHOL.typeToks cfolSign
        trForm = CFOL2IsabelleHOL.formTrCASL
        strs = CFOL2IsabelleHOL.getAssumpsToks cfolSign
        toIsabelle = foldFormula $ cspCaslTransRecord cfolSign
                     tyToks trForm strs vsm
        -- CFOL2IsabelleHOL.transFORMULA cfolSign tyToks trForm strs
    in toIsabelle $ rmPartial formulaNoSub
