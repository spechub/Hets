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

import qualified Common.OrderedMap as OMap
import qualified Data.Map as Map

import Common.AS_Annotation as AS_Anno
import Common.ProofUtils
import Data.Typeable
import Common.Result
import Common.Doc
import Common.DocUtils

import Data.List
import Data.Maybe (isJust)
import Data.Time (TimeOfDay,midnight)

import Control.Monad
import qualified Control.Concurrent as Concurrent

-- * pack sentences with their proofs

{- | instead of the sentence name (that will be the key into the order map)
the theorem status will be stored as attribute. The theorem status will be a
(wrapped) list of pairs (AnyComorphism, BasicProof) in G_theory, but a wrapped
list of (Proof_status proof_tree) in a logic specific 'Theory'. -}
type SenStatus a tStatus = SenAttr a (ThmStatus tStatus)

thmStatus :: SenStatus a tStatus -> [tStatus]
thmStatus = getThmStatus . senAttr

-- | the wrapped list of proof scripts or (AnyComorphism, BasicProof) pairs
data ThmStatus a = ThmStatus { getThmStatus :: [a] } deriving Show

instance Eq (ThmStatus a) where
    _ == _ = True

-- Ord must be consistent with Eq
instance Ord (ThmStatus a) where
    compare _ _ = EQ

instance (Show b, Pretty a) => Pretty (SenAttr a b) where
    pretty = printSenStatus pretty

printSenStatus :: (a -> Doc) -> SenAttr a b  -> Doc
printSenStatus fA = fA . sentence

emptySenStatus :: SenStatus a b
emptySenStatus = makeNamed (ThmStatus []) $ error "emptySenStatus"

instance Pretty a => Pretty (OMap.ElemWOrd a) where
    pretty = printOMapElemWOrd pretty

printOMapElemWOrd :: (a -> Doc) -> OMap.ElemWOrd a -> Doc
printOMapElemWOrd fA = fA . OMap.ele

-- | the map from lables to the theorem plus status (and position)
type ThSens a b = OMap.OMap String (SenStatus a b)

noSens :: ThSens a b
noSens = OMap.empty

mapThSensValueM :: Monad m => (a -> m b) -> ThSens a c -> m (ThSens b c)
mapThSensValueM f = foldM (\ m (k, v) -> do
  let oe =  OMap.ele v
  ns <- f $ sentence oe
  let ne = oe { sentence = ns }
  return $ Map.insert k v { OMap.ele = ne } m) Map.empty . Map.toList

mapThSensStatus :: (b -> c) -> ThSens a b -> ThSens a c
mapThSensStatus f = OMap.map (mapStatus f)

-- | join and disambiguate
--
-- * separate Axioms from Theorems
--
-- * don't merge sentences with same key but different contents?
joinSens :: (Ord a,Eq b) => ThSens a b -> ThSens a b -> ThSens a b
joinSens s1 s2 = let
    l1 = sortBy cmpSnd $ Map.toList s1
    updN n (_, e) = (n, e)
    m = OMap.size s1
    l2 = map (\ (x,e) -> (x,e {OMap.order = m + OMap.order e })) $
         sortBy cmpSnd $ Map.toList s2
    in Map.fromList $ mergeSens l1 $
                         genericDisambigSens fst updN (OMap.keysSet s1) l2
    where mergeSens [] l2 = l2
          mergeSens l1 [] = l1
          mergeSens l1@((k1, e1) : r1) l2@((k2, e2) : r2) =
              case cmpSenEle e1 e2 of
              LT -> (k1, e1) : mergeSens r1 l2
              EQ -> (k1, e1 { OMap.ele = (OMap.ele e1)
                                        { senAttr = ThmStatus $
                                              union (thmStatus $ OMap.ele e1)
                                                  (thmStatus $ OMap.ele e2)}})
                         : mergeSens r1 r2
              GT -> (k2, e2) : mergeSens l1 r2

cmpSnd :: (Ord a1) => (String, OMap.ElemWOrd (SenStatus a1 b))
       -> (String, OMap.ElemWOrd (SenStatus a1 b)) -> Ordering
cmpSnd (_, a) (_, b) = cmpSenEle a b

cmpSenEle :: (Ord a1) => OMap.ElemWOrd (SenStatus a1 b)
          -> OMap.ElemWOrd (SenStatus a1 b) -> Ordering
cmpSenEle x y = case (OMap.ele x,OMap.ele y) of
    (d1, d2) -> compare
      (sentence d1, isAxiom d1, isDef d1) (sentence d2, isAxiom d2, isDef d2)

diffSens :: (Ord a,Eq b) => ThSens a b -> ThSens a b -> ThSens a b
diffSens s1 s2 = let
    l1 = sortBy cmpSnd $ Map.toList s1
    l2 = sortBy cmpSnd $ Map.toList s2
    in Map.fromList $ diffS l1 l2
    where diffS [] _ = []
          diffS l1 [] = l1
          diffS l1@((k1, e1) : r1) l2@((_, e2) : r2) =
              case cmpSenEle e1 e2 of
              LT -> (k1, e1) : diffS r1 l2
              EQ -> diffS r1 r2
              GT -> diffS l1 r2

mapValue :: (a -> b) -> SenStatus a c -> SenStatus b c
mapValue f d = d { sentence = f $ sentence d }

mapStatus :: (b -> c) -> SenStatus a b -> SenStatus a c
mapStatus f d = d { senAttr = ThmStatus $ map f $ thmStatus d }

-- | sets the field isAxiom according to the boolean value;
-- if isAxiom is False for a sentence and set to True,
-- the field wasTheorem is set to True
markAsAxiom :: Ord a => Bool -> ThSens a b -> ThSens a b
markAsAxiom b = OMap.map $ \ d -> d
   { isAxiom = b
   , wasTheorem = b && (not (isAxiom d) || wasTheorem d) }

markAsGoal :: Ord a => ThSens a b -> ThSens a b
markAsGoal = markAsAxiom False

toNamedList :: ThSens a b -> [AS_Anno.Named a]
toNamedList = map (uncurry toNamed) . OMap.toList

toNamed :: String -> SenStatus a b -> AS_Anno.Named a
toNamed k s = s { AS_Anno.senAttr    = k }

-- | putting Sentences from a list into a map
toThSens :: Ord a => [AS_Anno.Named a] -> ThSens a b
toThSens = OMap.fromList . map
    ( \ v -> (AS_Anno.senAttr v, v { senAttr = ThmStatus [] }))
    . nameAndDisambiguate

-- | theories with a signature and sentences with proof states
data Theory sign sen proof_tree =
    Theory sign (ThSens sen (Proof_status proof_tree))

mapTheoryStatus :: (a->b) -> Theory sign sentence a
                   -> Theory sign sentence b
mapTheoryStatus f (Theory sig thSens) =
  Theory sig (mapThSensStatus (mapProofStatus f) thSens)

-- | theory morphisms between two theories
data TheoryMorphism sign sen mor proof_tree = TheoryMorphism
    { t_source :: Theory sign sen proof_tree
    , t_target :: Theory sign sen proof_tree
    , t_morphism :: mor }

-- e.g. the file name, or the script itself, or a configuration string
data Tactic_script = Tactic_script String deriving (Eq, Ord, Show)

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
  | Proved (Maybe Bool) -- ^ Just True means consistent; Nothing don't know
    deriving (Eq, Ord)
 -- needed for automated theorem provers like SPASS;
 -- provers like Isabelle set it to Nothing

instance Show GoalStatus where
    show gs = case gs of
        Open (Reason l) -> unlines $ "Open" : l
        Disproved -> "Disproved"
        Proved mc -> "Proved" ++ maybe ""
            ( \ c -> "(" ++ (if c then "" else "in") ++ "consistent)") mc

isOpenGoal :: GoalStatus -> Bool
isOpenGoal gs = case gs of
  Open _ -> True
  _ -> False

openGoalStatus :: GoalStatus
openGoalStatus = Open $ Reason []

-- | data type representing the proof status for a goal or
data Proof_status proof_tree = Proof_status
    { goalName :: String
    , goalStatus :: GoalStatus
    , usedAxioms :: [String] -- ^ used axioms
    , proverName :: String -- ^ name of prover
    , proofTree :: proof_tree
    , usedTime :: TimeOfDay
    , tacticScript :: Tactic_script }
    | Consistent Tactic_script
    deriving (Show, Eq, Ord)

{- | constructs an open proof status with basic information filled in;
     make sure to set proofTree to a useful value before you access it. -}
openProof_status :: Ord pt => String -- ^ name of the goal
                 -> String -- ^ name of the prover
                 -> pt -> Proof_status pt
openProof_status goalname provername proof_tree = Proof_status
   { goalName = goalname
   , goalStatus = openGoalStatus
   , usedAxioms = []
   , proverName = provername
   , proofTree = proof_tree
   , usedTime = midnight
   , tacticScript = Tactic_script "" }

mapProofStatus :: (a->b) -> Proof_status a -> Proof_status b
mapProofStatus f st = st {proofTree = f $ proofTree st}

isProvedStat :: Proof_status proof_tree -> Bool
isProvedStat pst = case pst of
    Consistent _ -> False
    _ -> isProvedGStat . goalStatus $ pst

isProvedGStat :: GoalStatus -> Bool
isProvedGStat gs = case gs of
    Proved _ -> True
    _ -> False

goalUsedInProof :: Monad m => Proof_status proof_tree -> m Bool
goalUsedInProof pst = case goalStatus pst of
    Proved m -> maybe (fail "don't know if goal was used") return m
    _ -> fail "not a proof"

-- | different kinds of prover interfaces
data ProverKind = ProveGUI | ProveCMDLautomatic

-- | determine if a prover kind is implemented
hasProverKind :: ProverKind -> ProverTemplate x s m y z -> Bool
hasProverKind pk pt = case pk of
    ProveGUI -> isJust $ proveGUI pt
    ProveCMDLautomatic ->
        isJust (proveCMDLautomatic pt) && isJust (proveCMDLautomaticBatch pt)

data FreeDefMorphism sentence morphism = FreeDefMorphism
  { freeDefMorphism :: morphism
  , pathFromFreeDef :: morphism
  , freeTheory :: [AS_Anno.Named sentence]
  , isCofree :: Bool }
  deriving (Eq, Show)

-- | prover or consistency checker
data ProverTemplate theory sentence morphism sublogics proof_tree = Prover
    { prover_name :: String,
      prover_sublogic :: sublogics,
      proveGUI :: Maybe (String -> theory -> [FreeDefMorphism sentence morphism]
                         -> IO ([Proof_status proof_tree])),
      -- input: imported theories, theory name, theory (incl. goals)
      -- output: proof status for goals and lemmas
      proveCMDLautomatic :: Maybe (String -> Tactic_script
                         -> theory -> [FreeDefMorphism sentence morphism]
                         ->IO (Result ([Proof_status proof_tree]))),
      -- input: theory name, Tactic_script,
      --        theory (incl. goals, but only the first one is tried)
      -- output: proof status for goals and lemmas
      proveCMDLautomaticBatch ::
          Maybe (Bool -- 1.
                 -> Bool -- 2.
                 -> Concurrent.MVar (Result [Proof_status proof_tree]) -- 3.
                 -> String -- 4.
                 -> Tactic_script  -- 5.
                 -> theory  -- 6.
                 -> [FreeDefMorphism sentence morphism]
                 -> IO (Concurrent.ThreadId,Concurrent.MVar ())) -- output
      -- input: 1. True means include proven theorems in subsequent
      --           proof attempts;
      --        2. True means save problem file for each goal;
      --        3. MVar reference to a Result [] or empty MVar,
      --           used to store the result of each attempt in the batch run;
      --        4. theory name;
      --        5. default Tactic_script;
      --        6. theory (incl. goals and
      --                   Open SenStatus for individual tactic_scripts)
      -- output: fst --> identifier of the batch thread for killing it,
      --                 after each proof attempt the result is stored in the
      --                 IOref
      --         snd --> MVar to wait for the end of the thread
    } deriving Typeable

type Prover sign sentence morphism sublogics proof_tree =
  ProverTemplate (Theory sign sentence proof_tree) sentence morphism sublogics proof_tree

mkProverTemplate :: String -> sublogics
                 -> (String -> theory -> [FreeDefMorphism sentence morphism] -> IO ([Proof_status proof_tree]))
                 -> ProverTemplate theory sentence morphism sublogics proof_tree
mkProverTemplate str sl fct = Prover
    { prover_name = str
    , prover_sublogic = sl
    , proveGUI = Just fct
    , proveCMDLautomatic = Nothing
    , proveCMDLautomaticBatch = Nothing }

type ConsChecker sign sentence sublogics morphism proof_tree =
    ProverTemplate (TheoryMorphism sign sentence morphism proof_tree)
        sentence morphism sublogics proof_tree
