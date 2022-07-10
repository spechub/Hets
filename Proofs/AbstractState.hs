{-# LANGUAGE ExistentialQuantification, DeriveDataTypeable #-}
{- |
Module      :  ./Proofs/AbstractState.hs
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
    ( ProverOrConsChecker (..)
    , G_prover (..)
    , G_proof_tree (..)
    , getProverName
    , getCcName
    , getCcBatch
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
    , getAxioms
    , getGoals
    , recalculateSublogicAndSelectedTheory
    , markProved
    , G_theory_with_prover (..)
    , G_theory_with_cons_checker (..)
    , prepareForProving
    , prepareForConsChecking
    , isSubElemG
    , pathToComorphism
    , getAllProvers
    , getUsableProvers
    , getConsCheckers
    , getAllConsCheckers
    , lookupKnownProver
    , lookupKnownConsChecker
    , autoProofAtNode
    ) where

import qualified Data.Map as Map
import Data.Maybe
import Data.Typeable

import Control.Concurrent.MVar
import Control.Monad.Trans
import Control.Monad
import qualified Control.Monad.Fail as Fail

import qualified Common.OrderedMap as OMap
import Common.Result as Result
import Common.ResultT
import Common.AS_Annotation
import Common.ExtSign
import Common.Utils
import Common.GraphAlgo (yen)

import Unsafe.Coerce (unsafeCoerce)

import Logic.Logic
import Logic.Prover
import Logic.Grothendieck
import Logic.Comorphism
import Logic.Coerce

import Comorphisms.KnownProvers

import Static.GTheory

-- import Interfaces.DataTypes (IntState)

-- * Provers

data ProverOrConsChecker = Prover G_prover
                         | ConsChecker G_cons_checker
                         deriving (Show)

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

usable :: G_prover -> IO Bool
usable (G_prover _ p) = fmap isNothing $ proverUsable p

coerceProver ::
  ( Logic lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
  , Logic lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
  , Fail.MonadFail m )
  => lid1 -> lid2 -> String
  -> Prover sign1 sentence1 morphism1 sublogics1 proof_tree1
  -> m (Prover sign2 sentence2 morphism2 sublogics2 proof_tree2)
coerceProver = primCoerce

data G_cons_checker =
  forall lid sublogics basic_spec sentence symb_items
    symb_map_items sign morphism symbol raw_symbol proof_tree
  . Logic lid sublogics basic_spec sentence symb_items
      symb_map_items sign morphism symbol raw_symbol proof_tree
  => G_cons_checker lid
       (ConsChecker sign sentence sublogics morphism proof_tree)
  deriving (Typeable)

instance Show G_cons_checker where
 show _ = "G_cons_checker "

getCcName :: G_cons_checker -> String
getCcName (G_cons_checker _ p) = ccName p

getCcBatch :: G_cons_checker -> Bool
getCcBatch (G_cons_checker _ p) = ccBatch p

usableCC :: G_cons_checker -> IO Bool
usableCC (G_cons_checker _ p) = fmap isNothing $ ccUsable p

coerceConsChecker ::
  ( Logic lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
  , Logic lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
  , Fail.MonadFail m )
  => lid1 -> lid2 -> String
  -> ConsChecker sign1 sentence1 sublogics1 morphism1 proof_tree1
  -> m (ConsChecker sign2 sentence2 sublogics2 morphism2 proof_tree2)
coerceConsChecker = primCoerce


-- | provers and consistency checkers for specific logics
data G_proof_tree =
  forall lid sublogics basic_spec sentence symb_items symb_map_items
    sign morphism symbol raw_symbol proof_tree
  . Logic lid sublogics basic_spec sentence symb_items symb_map_items
      sign morphism symbol raw_symbol proof_tree
  => G_proof_tree lid proof_tree
  deriving Typeable
instance Show G_proof_tree where
  show (G_proof_tree _ pt) = show pt

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
        currentTheory :: G_theory,
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
resetSelection s = case currentTheory s of
  G_theory _ _ _ _ sens _ ->
    let (aMap, gMap) = OMap.partition isAxiom sens
        gs = Map.keys gMap
    in s
    { selectedGoals = Map.keys gMap
    , includedAxioms = Map.keys aMap
    , includedTheorems = gs }

toAxioms :: ProofState -> [String]
toAxioms = map (\ (k, wTh) -> if wTh then "(Th) " ++ k else k)
  . getAxioms

getAxioms :: ProofState -> [(String, Bool)]
getAxioms = getThAxioms . currentTheory

getGoals :: ProofState -> [(String, Maybe BasicProof)]
getGoals = getThGoals . currentTheory

{- |
  Creates an initial State.
-}
initialState :: String
    -> G_theory
    -> KnownProversMap
    -> ProofState
initialState thN th pm = 
    case th of 
     G_theory lid _ _ _ _ _ -> resetSelection
       ProofState
         { theoryName = thN
         , currentTheory = th
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
                 let lidProver = default_prover lid
                 in if lidProver `elem` prvs 
                    then Just lidProver
                    else 
                     if defaultGUIProver `elem` prvs
                     then Just defaultGUIProver
                     else Nothing
         , selectedConsChecker = Nothing
         , selectedTheory = th }

logicId :: ProofState -> String
logicId s = case currentTheory s of
  G_theory lid _ _ _ _ _ -> language_name lid

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

data GPlainTheory =
  forall lid sublogics basic_spec sentence symb_items symb_map_items
    sign morphism symbol raw_symbol proof_tree
  . Logic lid sublogics basic_spec sentence symb_items symb_map_items
      sign morphism symbol raw_symbol proof_tree
  => GPlainTheory lid (Theory sign sentence proof_tree)

prepareForConsChecking :: ProofState
    -> (G_cons_checker, AnyComorphism)
    -> Result G_theory_with_cons_checker
prepareForConsChecking st (G_cons_checker lid4 p, co) = do
  GPlainTheory lidT th@(Theory sign'' _) <- prepareTheory st co
  incl <- subsig_inclusion lidT (empty_signature lidT) sign''
  let mor = TheoryMorphism
                    { tSource = emptyTheory lidT
                    , tTarget = th
                    , tMorphism = incl }
  p' <- coerceConsChecker lid4 lidT "" p
  return $ G_theory_with_cons_checker lidT mor p'


prepareTheory :: ProofState -> AnyComorphism -> Result GPlainTheory
prepareTheory st (Comorphism cid) = case selectedTheory st of
    G_theory lid _ (ExtSign sign _) _ sens _ -> do
        bTh' <- coerceBasicTheory lid (sourceLogic cid)
                   "Proofs.AbstractState.prepareTheory: basic theory"
                   (sign, toNamedList sens)
        (sign'', sens'') <- wrapMapTheory cid bTh'
        return . GPlainTheory (targetLogic cid) . Theory sign''
          $ toThSens sens''

{- | prepare the selected theory of the state for proving with the
given prover:

 * translation along the comorphism

 * all coercions

 * the lid is valid for the prover and the translated theory
-}
prepareForProving :: ProofState
    -> (G_prover, AnyComorphism)
    -> Result G_theory_with_prover
prepareForProving st (G_prover lid4 p, co) = do
  GPlainTheory lidT th <- prepareTheory st co
  p' <- coerceProver lid4 lidT "" p
  return $ G_theory_with_prover lidT th p'

-- | creates the currently selected theory
makeSelectedTheory :: ProofState -> G_theory
makeSelectedTheory s = case currentTheory s of
  G_theory lid syn sig si sens _ ->
    -- axiom map, goal map
    let (aMap, gMap) = OMap.partition isAxiom sens
        -- proven goals map
        pMap = OMap.filter isProvenSenStatus gMap
    in
    G_theory lid syn sig si
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

getConsCheckers :: [AnyComorphism] -> IO [(G_cons_checker, AnyComorphism)]
getConsCheckers = filterM (usableCC . fst) . getAllConsCheckers

getAllConsCheckers :: [AnyComorphism] -> [(G_cons_checker, AnyComorphism)]
getAllConsCheckers = concatMap (\ cm@(Comorphism cid) ->
    map (\ cc -> (G_cons_checker (targetLogic cid) cc, cm))
      $ cons_checkers $ targetLogic cid)

lookupKnownConsChecker :: Fail.MonadFail m => ProofState
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
               case filter (matchingCC pr_n) $ getAllConsCheckers
                    $ filter (lessSublogicComor sl) cms of
                 [] -> fail ("CMDL.ProverConsistency.lookupKnownConsChecker" ++
                                 ": no consistency checker found")
                 p : _ -> return p
       in maybe ( Fail.fail ("CMDL.ProverConsistency.lookupKnownConsChecker: " ++
                      "no matching known prover")) findCC mt


lookupKnownProver :: Fail.MonadFail m => ProofState -> ProverKind
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
    in maybe (Fail.fail "Proofs.InferBasic: no matching known prover")
             findProver mt

-- | Pairs each target prover of these comorphisms with its comorphism
getProvers :: ProverKind -> G_sublogics -> [AnyComorphism]
  -> [(G_prover, AnyComorphism)]
getProvers pk (G_sublogics lid sl) =
  foldl addProvers [] where
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

knownProvers :: LogicGraph -> ProverKind -> Map.Map G_sublogics [G_prover]
knownProvers lg pk =
 let l = Map.elems $ logics lg
 in foldl (\ m (Logic lid) -> foldl (\ m' p ->
     let lgx = G_sublogics lid (proverSublogic p)
         p' = G_prover lid p
     in case Map.lookup lgx m' of
         Just ps -> Map.insert lgx (p' : ps) m'
         Nothing -> Map.insert lgx [p'] m') m $
     filter (hasProverKind pk)
            (provers lid)) Map.empty l

unsafeCompComorphism :: AnyComorphism -> AnyComorphism -> AnyComorphism
unsafeCompComorphism c1 c2 = case compComorphism c1 c2 of
 Result _ (Just c_new) -> c_new
 r -> propagateErrors "Proofs.AbstractState.unsafeCompComorphism" r

isSubElemG :: G_sublogics -> G_sublogics -> Bool
isSubElemG (G_sublogics lid sl) (G_sublogics lid1 sl1) =
 Logic lid == Logic lid1 &&
 isSubElem sl (Unsafe.Coerce.unsafeCoerce sl1)

pathToComorphism :: ([((G_sublogics, t1), AnyComorphism)], (G_sublogics, t))
                    -> AnyComorphism
pathToComorphism (path, (G_sublogics lid sub, _)) =
 case path of
  [] -> Comorphism $ mkIdComorphism lid sub
  ((G_sublogics lid1 sub1, _), c) : cs ->
   foldl unsafeCompComorphism
    (Comorphism $ mkIdComorphism lid1 sub1)
    (c : snd (unzip cs))

getUsableProvers :: ProverKind -> G_sublogics -> LogicGraph
 -> IO [(G_prover, AnyComorphism)]
getUsableProvers pk start =
  filterM (usable . fst) . getAllProvers pk start

getAllProvers :: ProverKind -> G_sublogics -> LogicGraph
 -> [(G_prover, AnyComorphism)]
getAllProvers pk start lg =
  let kp = knownProvers lg pk
      g = logicGraph2Graph lg
  in concatMap (mkComorphism kp) $
      concatMap (\ end ->
       yen 10 (start, Nothing) (\ (l, _) -> isSubElemG l end) g)
       (Map.keys kp)
 where
  mkComorphism :: Map.Map G_sublogics [t2]
   -> ([((G_sublogics, t1), AnyComorphism)], (G_sublogics, t))
   -> [(t2, AnyComorphism)]
  mkComorphism kp path@(_, (end, _)) =
   let fullComorphism = pathToComorphism path
       cs = Map.toList $ Map.filterWithKey (\ l _ -> isSubElemG end l) kp
   in concatMap (\ x -> case x of
                        (_, ps) -> map (\ p -> (p, fullComorphism)) ps) cs

{- | the list of proof statuses is integrated into the goalMap of the state
after validation of the Disproved Statuses -}
markProved ::
  ( Logic lid sublogics basic_spec sentence symb_items symb_map_items
                sign morphism symbol raw_symbol proof_tree )
  => AnyComorphism -> lid -> [ProofStatus proof_tree]
  -> ProofState
  -> ProofState
markProved c lid status st = st
    { currentTheory = markProvedGoalMap c lid status (currentTheory st) }

-- | mark all newly proven goals with their proof tree
markProvedGoalMap ::
    ( Logic lid sublogics basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree )
    => AnyComorphism -> lid -> [ProofStatus proof_tree]
    -> G_theory -> G_theory
markProvedGoalMap c lid status th = case th of
  G_theory lid1 syn sig si thSens _ ->
      let updStat ps s = Just $
                s { senAttr = ThmStatus $ (c, BasicProof lid ps) : thmStatus s }
          upd pStat = OMap.update (updStat pStat) (goalName pStat)
      in G_theory lid1 syn sig si (foldl (flip upd) thSens status)
        startThId

autoProofAtNode ::
                   -- use theorems is subsequent proofs
                  Bool
                   -- Timeout Limit
                  -> Int
                   -- selected goals
                  -> [String]
                   -- selected axioms
                  -> [String]
                   -- Node selected for proving
                  -> G_theory
                   -- selected Prover and Comorphism
                  -> ( G_prover, AnyComorphism )
                   -- returns new GoalStatus for the Node
                  -> ResultT IO ((G_theory, [(String, String, String)]),
                                 (ProofState, [ProofStatus G_proof_tree]))
autoProofAtNode useTh timeout goals axioms g_th p_cm = do
      let knpr = propagateErrors "autoProofAtNode"
            $ knownProversWithKind ProveCMDLautomatic
          pf_st = initialState "" g_th knpr
          sg_st = if null goals then pf_st else pf_st
            { selectedGoals = filter (`elem` goals) $ selectedGoals pf_st }
          sa_st = if null axioms then sg_st else sg_st
            { includedAxioms = filter (`elem` axioms) $ includedAxioms sg_st }
          st = recalculateSublogicAndSelectedTheory sa_st
      -- try to prepare the theory
      if null $ selectedGoals st then fail "autoProofAtNode: no goals selected"
        else do
          (G_theory_with_prover lid1 th p) <- liftR $ prepareForProving st p_cm
          case proveCMDLautomaticBatch p of
            Nothing ->
              fail "autoProofAtNode: failed to init CMDLautomaticBatch"
            Just fn -> do
              let encapsulate_pt ps =
                   ps {proofTree = G_proof_tree lid1 $ proofTree ps}
              d <- lift $ do
                -- mVar to poll the prover for results
                answ <- newMVar (return [])
                (_, mV) <- fn useTh False answ (theoryName st)
                                       (TacticScript $ show timeout) th []
                takeMVar mV
                takeMVar answ
              case maybeResult d of
                Nothing -> fail "autoProofAtNode: proving failed"
                Just d' ->
                 return (( currentTheory $ markProved (snd p_cm) lid1 d' st
                         , map (\ ps -> ( goalName ps
                                        , show $ goalStatus ps
                                        , show $ proofTree ps)) d')
                         , (st, map encapsulate_pt d'))
