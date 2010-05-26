{- |
Module      :  $Header$
Description :  General datastructures for theorem prover interfaces
Copyright   :  (c) Till Mossakowski, Klaus Luettich, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (deriving Typeable)

General datastructures for theorem prover interfaces
-}

module Logic.Prover where

import Common.AS_Annotation as AS_Anno
import Common.Doc
import Common.DocUtils
import Common.Result
import Common.ProofUtils
import qualified Common.OrderedMap as OMap

import qualified Data.Map as Map
import Data.List
import Data.Maybe (isJust)
import Data.Time (TimeOfDay, midnight)
import Data.Typeable

import Control.Monad
import qualified Control.Concurrent as Concurrent

-- * pack sentences with their proofs

{- | instead of the sentence name (that will be the key into the order map)
the theorem status will be stored as attribute. The theorem status will be a
(wrapped) list of pairs (AnyComorphism, BasicProof) in G_theory, but a wrapped
list of (ProofStatus proof_tree) in a logic specific 'Theory'. -}
type SenStatus a tStatus = SenAttr a (ThmStatus tStatus)

thmStatus :: SenStatus a tStatus -> [tStatus]
thmStatus = getThmStatus . senAttr

-- | the wrapped list of proof scripts or (AnyComorphism, BasicProof) pairs
data ThmStatus a = ThmStatus { getThmStatus :: [a] } deriving (Show, Eq, Ord)

instance (Show b, Pretty a) => Pretty (SenAttr a b) where
    pretty = printSenStatus pretty

printSenStatus :: (a -> Doc) -> SenAttr a b -> Doc
printSenStatus = (. sentence)

emptySenStatus :: SenStatus a b
emptySenStatus = makeNamed (ThmStatus []) $ error "emptySenStatus"

instance Pretty a => Pretty (OMap.ElemWOrd a) where
    pretty = printOMapElemWOrd pretty

printOMapElemWOrd :: (a -> Doc) -> OMap.ElemWOrd a -> Doc
printOMapElemWOrd = (. OMap.ele)

-- | the map from lables to the theorem plus status (and position)
type ThSens a b = OMap.OMap String (SenStatus a b)

noSens :: ThSens a b
noSens = Map.empty

mapThSensValueM :: Monad m => (a -> m b) -> ThSens a c -> m (ThSens b c)
mapThSensValueM f = foldM (\ m (k, v) -> do
  let oe = OMap.ele v
  ns <- f $ sentence oe
  let ne = oe { sentence = ns }
  return $ Map.insert k v { OMap.ele = ne } m) Map.empty . Map.toList

{- | join and disambiguate

   * separate Axioms from Theorems

   * don't merge sentences with same key but different contents?
-}
joinSensAux :: (Ord a, Eq b) => ThSens a b -> ThSens a b
            -> (ThSens a b, [(String, String)])
joinSensAux s1 s2 = let
    l1 = Map.toList s1
    updN n (_, e) = (n, e)
    m = if null l1 then 0 else maximum $ map (OMap.order . snd) l1
    l2 = map (\ (x, e) -> (x, e {OMap.order = m + OMap.order e }))
         $ Map.toList s2
    sl2 = genericDisambigSens m fst updN (Map.keysSet s1) l2
    in (Map.fromList $ l1 ++ sl2,
         zipWith (\ (n1, _) (n2, _) -> (n1, n2)) l2 sl2)

joinSens :: (Ord a, Eq b) => ThSens a b -> ThSens a b -> ThSens a b
joinSens s1 = fst . joinSensAux s1

reduceSens :: (Ord a, Eq b) => ThSens a b -> ThSens a b
reduceSens =
    Map.fromList
  . map head
  . groupBy (\ (_, a) (_, b) -> sentence (OMap.ele a) == sentence (OMap.ele b))
  . sortBy cmpSnd
  . Map.toList

cmpSnd :: (Ord a1) => (String, OMap.ElemWOrd (SenStatus a1 b))
       -> (String, OMap.ElemWOrd (SenStatus a1 b)) -> Ordering
cmpSnd (_, a) (_, b) = cmpSenEle a b

cmpSenEle :: (Ord a1) => OMap.ElemWOrd (SenStatus a1 b)
          -> OMap.ElemWOrd (SenStatus a1 b) -> Ordering
cmpSenEle x y = case (OMap.ele x, OMap.ele y) of
    (d1, d2) -> compare
      (sentence d1, isAxiom d2, isDef d2) (sentence d2, isAxiom d1, isDef d1)

mapValue :: (a -> b) -> SenStatus a c -> SenStatus b c
mapValue f d = d { sentence = f $ sentence d }

{- | sets the field isAxiom according to the boolean value;
     if isAxiom is False for a sentence and set to True,
     the field wasTheorem is set to True.
-}
markAsAxiom :: Ord a => Bool -> ThSens a b -> ThSens a b
markAsAxiom b = OMap.map $ \ d -> d
   { isAxiom = b
   , wasTheorem = b && (not (isAxiom d) || wasTheorem d) }

markAsGoal :: Ord a => ThSens a b -> ThSens a b
markAsGoal = markAsAxiom False

toNamedList :: ThSens a b -> [AS_Anno.Named a]
toNamedList = map (uncurry toNamed) . OMap.toList

toNamed :: String -> SenStatus a b -> AS_Anno.Named a
toNamed k s = s { AS_Anno.senAttr = k }

-- | putting Sentences from a list into a map
toThSens :: Ord a => [AS_Anno.Named a] -> ThSens a b
toThSens = OMap.fromList . map
    ( \ v -> (AS_Anno.senAttr v, v { senAttr = ThmStatus [] }))
    . nameAndDisambiguate

-- | theories with a signature and sentences with proof states
data Theory sign sen proof_tree =
    Theory sign (ThSens sen (ProofStatus proof_tree))

-- e.g. the file name, or the script itself, or a configuration string
data TacticScript = TacticScript String deriving (Eq, Ord, Show)

-- | failure reason
data Reason = Reason [String]

instance Ord Reason where
  compare _ _ = EQ

instance Eq Reason where
  a == b = compare a b == EQ

-- | enumeration type representing the status of a goal
data GoalStatus =
    Open Reason -- ^ failure reason
  | Disproved
  | Proved Bool -- ^ True means consistent; False inconsistent
    deriving (Eq, Ord)

instance Show GoalStatus where
    show gs = case gs of
        Open (Reason l) -> unlines $ "Open" : l
        Disproved -> "Disproved"
        Proved c -> "Proved" ++ if c then "" else "(inconsistent)"

isOpenGoal :: GoalStatus -> Bool
isOpenGoal gs = case gs of
  Open _ -> True
  _ -> False

openGoalStatus :: GoalStatus
openGoalStatus = Open $ Reason []

-- | data type representing the proof status for a goal
data ProofStatus proof_tree = ProofStatus
    { goalName :: String
    , goalStatus :: GoalStatus
    , usedAxioms :: [String] -- ^ used axioms
    , usedProver :: String -- ^ name of prover
    , proofTree :: proof_tree
    , usedTime :: TimeOfDay
    , tacticScript :: TacticScript }
    deriving (Show, Eq, Ord)

{- | constructs an open proof status with basic information filled in;
     make sure to set proofTree to a useful value before you access it. -}
openProofStatus :: Ord pt => String -- ^ name of the goal
                -> String -- ^ name of the prover
                -> pt -> ProofStatus pt
openProofStatus goalname provername proof_tree = ProofStatus
   { goalName = goalname
   , goalStatus = openGoalStatus
   , usedAxioms = []
   , usedProver = provername
   , proofTree = proof_tree
   , usedTime = midnight
   , tacticScript = TacticScript "" }

isProvedStat :: ProofStatus proof_tree -> Bool
isProvedStat = isProvedGStat . goalStatus

isProvedGStat :: GoalStatus -> Bool
isProvedGStat gs = case gs of
    Proved _ -> True
    _ -> False

-- | different kinds of prover interfaces
data ProverKind = ProveGUI | ProveCMDLautomatic

-- | determine if a prover kind is implemented
hasProverKind :: ProverKind -> ProverTemplate x s m y z -> Bool
hasProverKind pk pt = case pk of
    ProveGUI -> isJust $ proveGUI pt
    ProveCMDLautomatic -> isJust $ proveCMDLautomaticBatch pt

data FreeDefMorphism sentence morphism = FreeDefMorphism
  { freeDefMorphism :: morphism
  , pathFromFreeDef :: morphism
  , freeTheory :: [AS_Anno.Named sentence]
  , isCofree :: Bool }
  deriving (Eq, Show)

-- | prover or consistency checker
data ProverTemplate theory sentence morphism sublogics proof_tree = Prover
    { proverName :: String,
      proverSublogic :: sublogics,
      proveGUI :: Maybe (String -> theory -> [FreeDefMorphism sentence morphism]
                         -> IO ( [ProofStatus proof_tree]
                               , [(Named sentence, ProofStatus proof_tree)])),
      {- input: imported theories, theory name, theory (incl. goals)
         output:
         fst --> proof status for goals and lemmas
         snd --> new lemmas (with proofs) -}
      proveCMDLautomaticBatch ::
          Maybe (Bool -- 1.
                 -> Bool -- 2.
                 -> Concurrent.MVar (Result [ProofStatus proof_tree]) -- 3.
                 -> String -- 4.
                 -> TacticScript  -- 5.
                 -> theory  -- 6.
                 -> [FreeDefMorphism sentence morphism]
                 -> IO (Concurrent.ThreadId, Concurrent.MVar ())) -- output
      {- input:
         1. True means include proven theorems in subsequent proof attempts;
         2. True means save problem file for each goal;
         3. MVar reference to a Result [] or empty MVar,
            used to store the result of each attempt in the batch run;
         4. theory name;
         5. default TacticScript;
         6. theory
            (incl. goals and Open SenStatus for individual tactic_scripts)
         7. ingoing free def morphisms
         output:
         fst --> identifier of the batch thread for killing it,
           after each proof attempt the result is stored in the IOref
         snd --> MVar to wait for the end of the thread -}
    } deriving Typeable

type Prover sign sentence morphism sublogics proof_tree =
  ProverTemplate (Theory sign sentence proof_tree)
    sentence morphism sublogics proof_tree

mkProverTemplate :: String -> sublogics
  -> (String -> theory -> [FreeDefMorphism sentence morphism]
      -> IO [ProofStatus proof_tree])
  -> ProverTemplate theory sentence morphism sublogics proof_tree
mkProverTemplate str sl fct = Prover
    { proverName = str
    , proverSublogic = sl
    , proveGUI = Just $ \ s t fs -> do
                ps <- fct s t fs
                return (ps, [])
    , proveCMDLautomaticBatch = Nothing }

mkAutomaticProver :: String -> sublogics
  -> (String -> theory -> [FreeDefMorphism sentence morphism]
      -> IO [ProofStatus proof_tree])
  -> (Bool -> Bool -> Concurrent.MVar (Result [ProofStatus proof_tree])
      -> String -> TacticScript -> theory -> [FreeDefMorphism sentence morphism]
      -> IO (Concurrent.ThreadId, Concurrent.MVar ()))
  -> ProverTemplate theory sentence morphism sublogics proof_tree
mkAutomaticProver str sl fct bFct =
  (mkProverTemplate str sl fct)
  { proveCMDLautomaticBatch = Just bFct }

-- | theory morphisms between two theories
data TheoryMorphism sign sen mor proof_tree = TheoryMorphism
    { tSource :: Theory sign sen proof_tree
    , tTarget :: Theory sign sen proof_tree
    , tMorphism :: mor }

data CCStatus proof_tree = CCStatus
  { ccProofTree :: proof_tree
  , ccUsedTime :: TimeOfDay
  , ccResult :: Maybe Bool }

data ConsChecker sign sentence sublogics morphism proof_tree = ConsChecker
  { ccName :: String
  , ccSublogic :: sublogics
  , ccBatch :: Bool -- True for batch checkers
  , ccNeedsTimer :: Bool -- True for checkers that ignore time limits
  , ccAutomatic :: String -- 1.
                 -> TacticScript  -- 2.
                 -> TheoryMorphism sign sentence morphism proof_tree  -- 3.
                 -> [FreeDefMorphism sentence morphism]  -- 4.
                 -> IO (CCStatus proof_tree) -- output
      -- input: 1. theory name
      -- 2. default TacticScript
      -- 3. theory morphism
      -- 5. ingoing free definition morphisms
      -- output: consistency result status
  } deriving Typeable

mkConsChecker :: String -> sublogics
  -> (String -> TacticScript -> TheoryMorphism sign sentence morphism proof_tree
      -> [FreeDefMorphism sentence morphism] -> IO (CCStatus proof_tree))
  -> ConsChecker sign sentence sublogics morphism proof_tree
mkConsChecker n sl f = ConsChecker
  { ccName = n
  , ccSublogic = sl
  , ccBatch = True
  , ccNeedsTimer = True
  , ccAutomatic = f }
