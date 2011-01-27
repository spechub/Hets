{-# LANGUAGE ExistentialQuantification, DeriveDataTypeable #-}
{- |
Module      :  $Header$
Description :  State data structure used by the goal management GUI.
Copyright   :  (c) Uni Bremen 2005-2007
License     :  GPLv2 or higher, see LICENSE.txt

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
    , getCcName
    , coerceProver
    , G_cons_checker (..)
    , coerceConsChecker
    , ProofActions (..)
    , ProofState (..)
    , sublogicOfTheory
    , logicId
    , initialState
    , resetSelection
    , toAxioms
    , getGoals
    , recalculateSublogicAndSelectedTheory
    , markProved
    , G_theory_with_prover (..)
    , G_theory_with_cons_checker (..)
    , prepareForProving
    , prepareForConsChecking
    , getAllProvers
    , getConsCheckers
    , lookupKnownProver
    , lookupKnownConsChecker
    , autoProofAtNode
    ) where

import qualified Data.Map as Map
import Data.Typeable

import Control.Concurrent.MVar

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
data G_prover =
  forall lid sublogics basic_spec sentence symb_items symb_map_items
    sign morphism symbol raw_symbol proof_tree
  . Logic lid sublogics basic_spec sentence symb_items symb_map_items
      sign morphism symbol raw_symbol proof_tree
  => G_prover lid (Prover sign sentence morphism sublogics proof_tree)
  deriving Typeable

instance Show G_prover where
  show = getProverName

getProverName :: G_prover -> String
getProverName (G_prover _ p) = proverName p

coerceProver ::
  ( Logic lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
  , Logic lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
  , Monad m )
  => lid1 -> lid2 -> String
  -> Prover sign1 sentence1 morphism1 sublogics1 proof_tree1
  -> m (Prover sign2 sentence2 morphism2 sublogics2 proof_tree2)
coerceProver = primCoerce

data G_cons_checker =
  forall lid sublogics basic_spec sentence symb_items symb_map_items
    sign morphism symbol raw_symbol proof_tree
  . Logic lid sublogics basic_spec sentence symb_items symb_map_items
      sign morphism symbol raw_symbol proof_tree
  => G_cons_checker lid
       (ConsChecker sign sentence sublogics morphism proof_tree)
  deriving Typeable

getCcName :: G_cons_checker -> String
getCcName (G_cons_checker _ p) = ccName p

coerceConsChecker ::
  ( Logic lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
  , Logic lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
  , Monad m )
  => lid1 -> lid2 -> String
  -> ConsChecker sign1 sentence1 sublogics1 morphism1 proof_tree1
  -> m (ConsChecker sign2 sentence2 sublogics2 morphism2 proof_tree2)
coerceConsChecker = primCoerce

-- | Possible actions for GUI which are manipulating ProofState
data ProofActions = ProofActions {
    -- | called whenever the "Prove" button is clicked
    proveF :: ProofState
      -> IO (Result.Result ProofState),
    -- | called whenever the "More fine grained selection" button is clicked
    fineGrainedSelectionF :: ProofState
      -> IO (Result.Result ProofState),
    -- | called whenever a (de-)selection occured for updating sublogic
    recalculateSublogicF :: ProofState
      -> IO ProofState
  }

{- |
  Represents the global state of the prover GUI.
-}
data ProofState =
     ProofState
      { -- | theory name
        theoryName :: String,
        -- | Grothendieck theory
        theory :: G_theory,
        -- | currently known provers
        proversMap :: KnownProversMap,
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
        -- | comorphisms fitting with sublogic of this G_theory
        comorphismsToProvers :: [(G_prover, AnyComorphism)],
        -- | which prover (if any) is currently selected
        selectedProver :: Maybe String,
        -- | which consistency checker (if any) is currently selected
        selectedConsChecker :: Maybe String,
        -- | theory based on selected goals, axioms and proven theorems
        selectedTheory :: G_theory
      } deriving Show

resetSelection :: ProofState -> ProofState
resetSelection s = case theory s of
  G_theory _ _ _ sens _ ->
    let (aMap, gMap) = OMap.partition isAxiom sens
    in s
    { selectedGoals = Map.keys gMap
    , includedAxioms = Map.keys aMap }

toAxioms :: ProofState -> [String]
toAxioms st = case theory st of
  G_theory _ _ _ sens _ -> map
    (\ (k, s) -> if wasTheorem s then "(Th) " ++ k else k)
    $ OMap.toList $ OMap.filter isAxiom sens

getGoals :: ProofState -> [(String, Maybe BasicProof)]
getGoals s = case theory s of
  G_theory _ _ _ sens _ -> map toGoal . OMap.toList
    $ OMap.filter (not . isAxiom) sens
  where toGoal (n, st) = let ts = thmStatus st in
               (n, if null ts then Nothing else Just $ maximum $ map snd ts)

{- |
  Creates an initial State.
-}
initialState :: String
    -> G_theory
    -> KnownProversMap
    -> ProofState
initialState thN th pm = resetSelection
       ProofState
         { theoryName = thN
         , theory = th
         , proversMap = pm
         , selectedGoals = []
         , includedAxioms = []
         , includedTheorems = []
         , proverRunning = False
         , accDiags = []
         , comorphismsToProvers = []
         , selectedProver =
             let prvs = Map.keys pm
             in if null prvs
                then Nothing
                else
                    if defaultGUIProver `elem` prvs
                    then Just defaultGUIProver
                    else Nothing
         , selectedConsChecker = Nothing
         , selectedTheory = th }

logicId :: ProofState -> String
logicId s = case theory s of
  G_theory lid _ _ _ _ -> language_name lid

sublogicOfTheory :: ProofState -> G_sublogics
sublogicOfTheory = sublogicOfTh . selectedTheory

data G_theory_with_cons_checker =
  forall lid sublogics basic_spec sentence symb_items symb_map_items
    sign morphism symbol raw_symbol proof_tree
  . Logic lid sublogics basic_spec sentence symb_items symb_map_items
      sign morphism symbol raw_symbol proof_tree
  => G_theory_with_cons_checker lid
       (TheoryMorphism sign sentence morphism proof_tree)
       (ConsChecker sign sentence sublogics morphism proof_tree)

-- | a Grothendieck pair of prover and theory which are in the same logic
data G_theory_with_prover =
  forall lid sublogics basic_spec sentence symb_items symb_map_items
    sign morphism symbol raw_symbol proof_tree
  . Logic lid sublogics basic_spec sentence symb_items symb_map_items
      sign morphism symbol raw_symbol proof_tree
  => G_theory_with_prover lid
       (Theory sign sentence proof_tree)
       (Prover sign sentence morphism sublogics proof_tree)

prepareForConsChecking :: ProofState
    -> (G_cons_checker, AnyComorphism)
    -> Result G_theory_with_cons_checker
prepareForConsChecking st (G_cons_checker lid4 p, Comorphism cid) =
    case selectedTheory st of
     G_theory lid (ExtSign sign _) _ sens _ ->
       do
        let lidT = targetLogic cid
        bTh' <- coerceBasicTheory lid (sourceLogic cid)
                   "Proofs.InferBasic.callProver: basic theory"
                   (sign, toNamedList sens)
        (sign'', sens'') <- wrapMapTheory cid bTh'
        incl <- subsig_inclusion lidT (empty_signature lidT) sign''
        let mor = TheoryMorphism
                    { tSource = emptyTheory lidT
                    , tTarget = Theory sign'' (toThSens sens'')
                    , tMorphism = incl }
        p' <- coerceConsChecker lid4 lidT "" p
        return $ G_theory_with_cons_checker lidT mor p'


{- | prepare the selected theory of the state for proving with the
given prover:

 * translation along the comorphism

 * all coercions

 * the lid is valid for the prover and the translated theory
-}
prepareForProving :: ProofState
    -> (G_prover, AnyComorphism)
    -> Result G_theory_with_prover
prepareForProving st (G_prover lid4 p, Comorphism cid) =
    case selectedTheory st of
    G_theory lid (ExtSign sign _) _ sens _ ->
      do
        let lidT = targetLogic cid
        bTh' <- coerceBasicTheory lid (sourceLogic cid)
                   "Proofs.InferBasic.callProver: basic theory"
                   (sign, toNamedList sens)
        (sign'', sens'') <- wrapMapTheory cid bTh'
        p' <- coerceProver lid4 lidT "" p
        return $
           G_theory_with_prover lidT (Theory sign'' (toThSens sens'')) p'

-- | creates the currently selected theory
makeSelectedTheory :: ProofState -> G_theory
makeSelectedTheory s = case theory s of
  G_theory lid sig si sens _ ->
    let (aMap, gMap) = OMap.partition isAxiom sens
        pMap = OMap.filter isProvenSenStatus gMap
    in
    G_theory lid sig si
      (Map.unions
        [ filterMapWithList (selectedGoals s) gMap
        , filterMapWithList (includedAxioms s) aMap
        , markAsAxiom True $ filterMapWithList (includedTheorems s) pMap
        ]) startThId

{- |
  recalculation of sublogic upon (de)selection of goals, axioms and
  proven theorems
-}
recalculateSublogicAndSelectedTheory :: ProofState -> ProofState
recalculateSublogicAndSelectedTheory st = let
  sTh = makeSelectedTheory st
  sLo = sublogicOfTh sTh
  in st
    { selectedTheory = sTh
    , proversMap = shrinkKnownProvers sLo $ proversMap st }

getConsCheckers :: [AnyComorphism] -> [(G_cons_checker, AnyComorphism)]
getConsCheckers = concatMap (\ cm@(Comorphism cid) ->
    map (\ cc -> (G_cons_checker (targetLogic cid) cc, cm))
      $ cons_checkers $ targetLogic cid)

lookupKnownConsChecker :: Monad m => ProofState
    -> m (G_cons_checker, AnyComorphism)
lookupKnownConsChecker st =
       let sl = sublogicOfTh (selectedTheory st)
           mt = do
                 pr_s <- selectedConsChecker st
                 ps <- Map.lookup pr_s (proversMap st)
                 return (pr_s, ps)
           matchingCC s (gp, _) = case gp of
                                  G_cons_checker _ p -> ccName p == s
           findCC (pr_n, cms) =
               case filter (matchingCC pr_n) $ getConsCheckers
                    $ filter (lessSublogicComor sl) cms of
                 [] -> fail ("CMDL.ProverConsistency.lookupKnownConsChecker" ++
                                 ": no consistency checker found")
                 p : _ -> return p
       in maybe ( fail ("CMDL.ProverConsistency.lookupKnownConsChecker: " ++
                      "no matching known prover")) findCC mt


lookupKnownProver :: Monad m => ProofState -> ProverKind
    -> m (G_prover, AnyComorphism)
lookupKnownProver st pk =
    let sl = sublogicOfTh (selectedTheory st)
        mt = do -- Monad Maybe
           pr_s <- selectedProver st
           ps <- Map.lookup pr_s (proversMap st)
           return (pr_s, ps)
        matchingPr s (gp, _) = case gp of
          G_prover _ p -> proverName p == s
        findProver (pr_n, cms) =
            case filter (matchingPr pr_n) $ getProvers pk sl
                 $ filter (lessSublogicComor sl) cms of
               [] -> fail "Proofs.InferBasic: no prover found"
               p : _ -> return p
    in maybe (fail "Proofs.InferBasic: no matching known prover")
             findProver mt

-- | Pairs each target prover of these comorphisms with its comorphism
getProvers :: ProverKind -> G_sublogics -> [AnyComorphism]
  -> [(G_prover, AnyComorphism)]
getProvers pk (G_sublogics lid sl) =
  foldl addProvers [] . filter hasModelExpansion where
  addProvers acc cm = case cm of
    Comorphism cid -> let
      slid = sourceLogic cid
      tlid = targetLogic cid
      in acc ++ foldl
             (\ l p ->
                  if hasProverKind pk p
                    && language_name lid == language_name slid
                         && maybe False (flip isSubElem $ proverSublogic p)
                           (mapSublogic cid $ forceCoerceSublogic lid slid sl)
                  then (G_prover tlid p, cm) : l else l)
             [] (provers tlid)

getAllProvers :: ProverKind -> G_sublogics -> LogicGraph
  -> [(G_prover, AnyComorphism)]
getAllProvers pk sl lg = getProvers pk sl $ findComorphismPaths lg sl

{- | the list of proof statuses is integrated into the goalMap of the state
after validation of the Disproved Statuses -}
markProved ::
  ( Logic lid sublogics basic_spec sentence symb_items symb_map_items
                sign morphism symbol raw_symbol proof_tree )
  => AnyComorphism -> lid -> [ProofStatus proof_tree]
  -> ProofState
  -> ProofState
markProved c lid status st = st
    { theory = markProvedGoalMap c lid status (theory st) }

-- | mark all newly proven goals with their proof tree
markProvedGoalMap ::
    ( Logic lid sublogics basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree )
    => AnyComorphism -> lid -> [ProofStatus proof_tree]
    -> G_theory -> G_theory
markProvedGoalMap c lid status th = case th of
  G_theory lid1 sig si thSens _ ->
      let updStat ps s = Just $
                s { senAttr = ThmStatus $ (c, BasicProof lid ps) : thmStatus s }
          upd pStat = OMap.update (updStat pStat) (goalName pStat)
      in G_theory lid1 sig si (foldl (flip upd) thSens status)
        startThId

autoProofAtNode :: -- use theorems is subsequent proofs
                    Bool
                   -- Timeout Limit
                  -> Int
                   -- Node selected for proving
                  -> G_theory
                   -- selected Prover and Comorphism
                  -> ( G_prover, AnyComorphism )
                   -- returns new GoalStatus for the Node
                  -> IO (Maybe G_theory, Maybe [(String, String)])
autoProofAtNode useTh timeout g_th p_cm = do
      let knpr = propagateErrors "autoProofAtNode"
            $ knownProversWithKind ProveCMDLautomatic
          pf_st = initialState "" g_th knpr
          st = recalculateSublogicAndSelectedTheory pf_st
      -- try to prepare the theory
      if null $ selectedGoals st then return (Nothing, Just []) else
        case maybeResult $ prepareForProving st p_cm of
        Nothing -> return (Nothing, Nothing)
        Just (G_theory_with_prover lid1 th p) ->
          case proveCMDLautomaticBatch p of
            Nothing -> return (Nothing, Nothing)
            Just fn -> do
              -- mVar to poll the prover for results
              answ <- newMVar (return [])
              (_, mV) <- fn useTh False answ (theoryName st)
                                       (TacticScript $ show timeout) th []
              takeMVar mV
              d <- takeMVar answ
              return $ case maybeResult d of
                Nothing -> (Nothing, Nothing)
                Just d' ->
                  ( Just $ theory $ markProved (snd p_cm) lid1 d' st
                  , Just $ map (\ ps -> (goalName ps, show $ goalStatus ps)) d')
