{-# LANGUAGE ExistentialQuantification, DeriveDataTypeable #-}
{- |
Module      :  $Header$
Description :  State data structure used by the goal management GUI.
Copyright   :  (c) Uni Bremen 2005-2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Logic)

The 'ProofState' data structure abstracts the GUI implementation details
away by allowing callback function to use it as the sole input and output.
It is also used by the CMDL interface.
-}

module Proofs.AbstractState
    ( G_prover (..)
    , getProverName
    , coerceProver
    , G_cons_checker (..)
    , coerceConsChecker
    , ProofActions (..)
    , ProofState (..)
    , initialState
    , selectedGoalMap
    , axiomMap
    , recalculateSublogicAndSelectedTheory
    , GetPName (..)
    , markProved
    , markProvedGoalMap
    , G_theory_with_prover (..)
    , G_theory_with_cons_checker (..)
    , prepareForProving
    , prepareForConsChecking
    , getProvers
    , getConsCheckers
    , lookupKnownProver
    , lookupKnownConsChecker
    ) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Typeable

import qualified Common.OrderedMap as OMap
import Common.Result as Result
import Common.AS_Annotation
import Common.ExtSign
import Common.Utils

import Logic.Logic
import Logic.Prover
import Logic.Grothendieck
import Logic.Comorphism
import Logic.Coerce

import Comorphisms.KnownProvers

import Static.GTheory

-- * Provers

-- | provers and consistency checkers for specific logics
data G_prover = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
       G_prover lid (Prover sign sentence morphism sublogics proof_tree)
  deriving Typeable

getProverName :: G_prover -> String
getProverName (G_prover _ p) = proverName p

coerceProver ::
  (Logic  lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
   Logic  lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2,
   Monad m) => lid1 -> lid2 -> String
      -> Prover sign1 sentence1 morphism1 sublogics1 proof_tree1
      -> m (Prover sign2 sentence2 morphism2 sublogics2 proof_tree2)
coerceProver = primCoerce

data G_cons_checker = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
       G_cons_checker lid
                (ConsChecker sign sentence sublogics morphism proof_tree)
  deriving Typeable

coerceConsChecker ::
  (Logic  lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
   Logic  lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2,
   Monad m) => lid1 -> lid2 -> String
      -> ConsChecker sign1 sentence1 sublogics1 morphism1 proof_tree1
      -> m (ConsChecker sign2 sentence2 sublogics2 morphism2 proof_tree2)
coerceConsChecker = primCoerce

-- | Possible actions for GUI which are manipulating ProofState
data ProofActions lid sentence = ProofActions {
    -- | called whenever the "Prove" button is clicked
    proveF :: ProofState lid sentence
           -> IO (Result.Result (ProofState lid sentence)),
    -- | called whenever the "More fine grained selection" button is clicked
    fineGrainedSelectionF :: ProofState lid sentence
                          -> IO (Result.Result (ProofState lid sentence)),
    -- | called whenever a (de-)selection occured for updating sublogic
    recalculateSublogicF :: ProofState lid sentence
                         -> IO (ProofState lid sentence)
  }

{- |
  Represents the global state of the prover GUI.
-}
data ProofState lid sentence =
     ProofState
      { -- | theory name
        theoryName :: String,
        -- | Grothendieck theory
        theory :: G_theory,
        -- | translated theory
        -- | logic id associated with following maps
        logicId :: lid,
        -- | sublogic of initial G_theory
        sublogicOfTheory :: G_sublogics,
        -- | last used sublogic to determine fitting comorphisms
        lastSublogic :: G_sublogics,
        -- | goals are stored in a separate map
        goalMap :: ThSens sentence (AnyComorphism,BasicProof),
        -- | currently known provers
        proversMap :: KnownProversMap,
        -- | comorphisms fitting with sublogic of this G_theory
        comorphismsToProvers :: [(G_prover,AnyComorphism)],
        -- | currently selected goals
        selectedGoals :: [String],
        -- | axioms to include for the proof
        includedAxioms :: [String],
        -- | theorems to include for the proof
        includedTheorems :: [String],
        -- | whether a prover is running or not
        proverRunning :: Bool,
        -- | accumulated Diagnosis during Proofs
        accDiags :: [Diagnosis],
        -- | which prover (if any) is currently selected
        selectedProver :: Maybe String,
        -- | which consistency checker (if any) is currently selected
        selectedConsChecker :: Maybe String,
        -- | Grothendieck theory based upon currently selected goals, axioms
        --   and proven theorems
        selectedTheory :: G_theory
      }

{- |
  Creates an initial State.
-}
initialState ::
    (Logic  lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                 sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
     Monad m) =>
                lid1
              -> String
             -> G_theory
             -> KnownProversMap
             -> [(G_prover,AnyComorphism)]
             -> m (ProofState lid1 sentence1)
initialState lid1 thN th@(G_theory lid2 sig ind thSens _) pm cms =
    do let (aMap,gMap) = Map.partition (isAxiom . OMap.ele) thSens
           g_th = G_theory lid2 sig ind aMap startThId
           sublTh = sublogicOfTh th
       gMap' <- coerceThSens lid2 lid1 "creating initial state" gMap
       return ProofState { theoryName = thN,
                           theory = g_th,
                           sublogicOfTheory = sublTh,
                           lastSublogic = sublTh,
                           logicId = lid1,
                           goalMap = gMap',
                           proversMap = pm,
                           comorphismsToProvers = cms,
                           selectedGoals = OMap.keys gMap',
                           includedAxioms = OMap.keys aMap,
                           includedTheorems = OMap.keys gMap,
                           accDiags = [],
                           proverRunning = False,
                           selectedProver =
                               let prvs = Map.keys pm
                               in if null prvs
                                  then Nothing
                                  else
                                    if defaultGUIProver `elem` prvs
                                       then Just defaultGUIProver
                                       else Nothing
                          ,selectedConsChecker = Nothing
                          ,selectedTheory = g_th
                         }


data G_theory_with_cons_checker =
    forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
    G_theory_with_cons_checker lid
                  (TheoryMorphism sign sentence morphism proof_tree)
                  (ConsChecker sign sentence sublogics morphism proof_tree)

-- | a Grothendieck pair of prover and theory which are in the same logic
data G_theory_with_prover =
    forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
  G_theory_with_prover lid
                (Theory sign sentence proof_tree)
                (Prover sign sentence morphism sublogics proof_tree)


prepareForConsChecking :: (Logic lid sublogics1
                              basic_spec1
                              sentence
                              symb_items1
                              symb_map_items1
                              sign1
                              morphism1
                              symbol1
                              raw_symbol1
                              proof_tree1) =>
                         ProofState lid sentence
                      -> (G_cons_checker, AnyComorphism)
                      -> Result G_theory_with_cons_checker
prepareForConsChecking st (G_cons_checker lid4 p, Comorphism cid) =
    case selectedTheory st of
     G_theory lid1 (ExtSign sign _) _ sens _ ->
       do
        let lidT = targetLogic cid
        bTh' <- coerceBasicTheory lid1 (sourceLogic cid)
                   "Proofs.InferBasic.callProver: basic theory"
                   (sign, toNamedList sens)
        (sign'',sens'') <- wrapMapTheory cid bTh'
        incl <- subsig_inclusion lidT (empty_signature lidT) sign''
        let mor = TheoryMorphism
                    { tSource = emptyTheory lidT,
                      tTarget = Theory sign'' (toThSens sens''),
                      tMorphism = incl}
        p' <- coerceConsChecker lid4 lidT "" p
        return  $
          G_theory_with_cons_checker lidT mor p'


-- | prepare the selected theory of the state for proving with the
-- given prover:
--
-- * translation along the comorphism
--
-- * all coercions
--
-- * the lid is valid for the prover and the translated theory
prepareForProving :: (Logic lid sublogics1
                            basic_spec1
                            sentence
                            symb_items1
                            symb_map_items1
                            sign1
                            morphism1
                            symbol1
                            raw_symbol1
                            proof_tree1) =>
                      ProofState lid sentence
                  -> (G_prover,AnyComorphism)
                  -> Result G_theory_with_prover
prepareForProving st (G_prover lid4 p, Comorphism cid) =
    case selectedTheory st of
    G_theory lid1 (ExtSign sign _) _ sens _ ->
      do
        let lidT = targetLogic cid
        bTh' <- coerceBasicTheory lid1 (sourceLogic cid)
                   "Proofs.InferBasic.callProver: basic theory"
                   (sign, toNamedList sens)
        (sign'',sens'') <- wrapMapTheory cid bTh'
        p' <- coerceProver lid4 lidT "" p
        return $
           G_theory_with_prover lidT (Theory sign'' (toThSens sens'')) p'

-- | returns the map of currently selected goals
selectedGoalMap :: ProofState lid sentence
                -> ThSens sentence (AnyComorphism,BasicProof)
selectedGoalMap st = filterMapWithList (selectedGoals st) (goalMap st)

-- | returns the axioms of the state coerced into the state's logicId
axiomMap ::
    (Logic  lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                 sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
     Monad m) =>
       ProofState lid1 sentence1
    -> m (ThSens sentence1 (AnyComorphism,BasicProof))
axiomMap s =
    case theory s of
    G_theory lid1 _ _ aM _ ->
        coerceThSens lid1 (logicId s) "Proofs.GUIState.axiomMap" aM

{- |
  recalculation of sublogic upon (de)selection of goals, axioms and
  proven theorems
-}
recalculateSublogicAndSelectedTheory :: (Logic lid sublogics1
                   basic_spec1
                   sentence
                   symb_items1
                   symb_map_items1
                   sign1
                   morphism1
                   symbol1
                   raw_symbol1
                   proof_tree1) =>
       ProofState lid sentence -> ProofState lid sentence
recalculateSublogicAndSelectedTheory st =
  case theory st of
    G_theory lid1 sign _ sens _ ->
          -- coerce goalMap
        case coerceThSens (logicId st) lid1 "" $ goalMap st of
          Nothing -> error
            "Proofs.InferBasic.recalculateSublogic: selected goals"
          Just ths -> let
            -- partition goalMap
            (sel_goals, other_goals) =
                let selected k _ = Set.member k s
                    s = Set.fromList (selectedGoals st)
                in Map.partitionWithKey selected ths
            -- to properly rerun proofs only proven theorems
            -- before the first open one should be included!
            provenThs = OMap.filter isProvenSenStatus other_goals
            sel_provenThs = markAsAxiom True $
                            filterMapWithList (includedTheorems st) provenThs
            sel_sens = filterMapWithList (includedAxioms st) sens
            selAxs = Map.union sel_sens sel_provenThs
            currentThSens = Map.union selAxs sel_goals
            sTh = G_theory lid1 sign startSigId currentThSens startThId
            sLo = sublogicOfTh sTh
            in st { sublogicOfTheory = sLo
                  , selectedTheory = sTh
                  , proversMap = shrinkKnownProvers sLo (proversMap st) }

class GetPName a where
    getPName :: a -> String

instance GetPName G_prover where
    getPName = getProverName

instance GetPName G_cons_checker where
    getPName (G_cons_checker _ p) = ccName p


getConsCheckers :: [AnyComorphism] -> [(G_cons_checker, AnyComorphism)]
getConsCheckers = concatMap (\ cm@(Comorphism cid) ->
    map (\ cc -> (G_cons_checker (targetLogic cid) cc, cm))
      $ cons_checkers $ targetLogic cid)

lookupKnownConsChecker :: (Logic lid sublogics1
                            basic_spec1
                            sentence
                            symb_items1
                            symb_map_items1
                            sign1
                            morphism1
                            symbol1
                            raw_symbol1
                            proof_tree1
                         , Monad m) =>
                         ProofState lid sentence
                         -> m (G_cons_checker, AnyComorphism)
lookupKnownConsChecker st =
       let sl = sublogicOfTheory st
           mt = do
                 pr_s <- selectedConsChecker st
                 ps <- Map.lookup pr_s (proversMap st)
                 return (pr_s, ps)
           matchingCC s (gp,_) = case gp of
                                  G_cons_checker _ p -> ccName p == s
           findCC (pr_n,cms) =
               case filter (matchingCC pr_n) $ getConsCheckers
                    $ filter (lessSublogicComor sl) cms of
                 [] -> fail ("CMDL.ProverConsistency.lookupKnownConsChecker"++
                                 ": no consistency checker found")
                 p:_ -> return p
       in maybe ( fail ("CMDL.ProverConsistency.lookupKnownConsChecker: "++
                      "no matching known prover")) findCC mt


lookupKnownProver :: (Logic lid sublogics1
                       basic_spec1
                       sentence
                       symb_items1
                       symb_map_items1
                       sign1
                       morphism1
                       symbol1
                       raw_symbol1
                       proof_tree1
                , Monad m) =>
                ProofState lid sentence -> ProverKind
             -> m (G_prover,AnyComorphism)
lookupKnownProver st pk =
    let sl = sublogicOfTheory st
        mt = do -- Monad Maybe
           pr_s <- selectedProver st
           ps <- Map.lookup pr_s (proversMap st)
           return (pr_s, ps)
        matchingPr s (gp, _) = case gp of
          G_prover _ p -> proverName p == s
        findProver (pr_n, cms) =
            case filter (matchingPr pr_n) $ getProvers pk (Just sl)
                 $ filter (lessSublogicComor sl) cms of
               [] -> fail "Proofs.InferBasic: no prover found"
               p : _ -> return p
    in maybe (fail "Proofs.InferBasic: no matching known prover")
             findProver mt

-- | Pairs each target prover of these comorphisms with its comorphism
getProvers :: ProverKind -> Maybe G_sublogics
           -> [AnyComorphism] -> [(G_prover, AnyComorphism)]
getProvers pk msl = foldl addProvers []
    where addProvers acc cm = case cm of
              Comorphism cid -> let
                slid = sourceLogic cid
                tlid = targetLogic cid
                in acc ++ foldl (\ l p ->
                  if hasProverKind pk p
                    && case msl of
                      Just (G_sublogics lid sl) ->
                        language_name lid == language_name slid
                         && maybe False (flip isSubElem $ proverSublogic p)
                           (mapSublogic cid $ forceCoerceSublogic lid slid sl)
                      Nothing -> True
                  then (G_prover tlid p, cm) : l else l)
                [] (provers tlid)

-- | the list of proof statuses is integrated into the goalMap of the state
-- after validation of the Disproved Statuses
markProved :: (Logic lid1 sublogics1
                     basic_spec1 sentence1 symb_items1 symb_map_items1
                     sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
               Logic lid sublogics
                     basic_spec sentence symb_items symb_map_items
                     sign morphism symbol raw_symbol proof_tree) =>
       AnyComorphism -> lid -> [ProofStatus proof_tree]
    -> ProofState lid1 sentence1
    -> ProofState lid1 sentence1
markProved c lid status st =
      st { goalMap = markProvedGoalMap c lid
                                       (filterValidProofStatus st status)
                                       (goalMap st)}

-- | mark all newly proven goals with their proof tree
markProvedGoalMap :: (Ord a, Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree) =>
       AnyComorphism -> lid -> [ProofStatus proof_tree]
    -> ThSens a (AnyComorphism, BasicProof)
    -> ThSens a (AnyComorphism, BasicProof)
markProvedGoalMap c lid status thSens = foldl upd thSens status
    where upd m pStat = OMap.update (updStat pStat) (goalName pStat) m
          updStat ps s = Just $
                s { senAttr = ThmStatus $ (c, BasicProof lid ps) : thmStatus s}

filterValidProofStatus :: (Logic lid sublogics1
                                  basic_spec1
                                  sentence
                                  symb_items1
                                  symb_map_items1
                                  sign1
                                  morphism1
                                  symbol1
                                  raw_symbol1
                                  proof_tree1) =>
                           ProofState lid sentence
                        -> [ProofStatus proof_tree]
                        -> [ProofStatus proof_tree]
filterValidProofStatus st =
    case selectedTheory st of
      G_theory _ _ _ sens _ ->
          filter (provedOrDisproved (includedAxioms st == OMap.keys sens))
    where provedOrDisproved allSentencesIncluded senStat =
              isProvedStat senStat ||
             (allSentencesIncluded && case goalStatus senStat of
                                      Disproved -> True
                                      _ -> False)
