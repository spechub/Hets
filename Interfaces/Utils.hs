{- |
Module      :$Header$
Description : utilitary functions
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

Interfaces.Utils contains different utilitary functions for the
abstract interface

-}

module Interfaces.Utils
         ( getAllNodes
         , getAllEdges
         , initNodeInfo
         , emptyIntIState
         , addProveToHist
         , proofTreeToProve
         , wasProved
         , convertGoal
         , parseTimeLimit
         , mergeGoals
         , emptyCommandHistory
         , addCommandHistoryToState
         ) where


import Interfaces.DataTypes
import Interfaces.GenericATPState
import Data.Graph.Inductive.Graph
import Static.DevGraph
import Proofs.AbstractState
import Logic.Logic
import Common.LibName
import Data.List (isPrefixOf, stripPrefix)
import Driver.Options(rmSuffix)
import Data.Maybe (fromMaybe)
import System.Directory (getCurrentDirectory)
import Data.IORef
import Logic.Comorphism (AnyComorphism(..))
import Logic.Prover
import Proofs.AbstractState
import Static.GTheory (G_theory(..))

import Common.OrderedMap (keys)
import Common.Utils(joinWith, splitOn)
import Common.Result

-- | Returns the list of all nodes, if it is not up to date
-- the function recomputes the list
getAllNodes :: IntIState  -> [LNode DGNodeLab]
getAllNodes st
 = labNodesDG $ lookupDGraph (i_ln st) (i_libEnv st)

-- | Returns the list of all edges, if it is not up to date
-- the funcrion recomputes the list
getAllEdges :: IntIState -> [LEdge DGLinkLab]
getAllEdges st
 = labEdgesDG $ lookupDGraph (i_ln st) (i_libEnv st)


-- | Constructor for CMDLProofGUIState datatype
initNodeInfo:: (Logic lid1 sublogics1
         basic_spec1 sentence1 symb_items1 symb_map_items1
         sign1 morphism1 symbol1 raw_symbol1 proof_tree1) =>
         ProofState lid1 sentence1 -> Int
         -> Int_NodeInfo
initNodeInfo = Element

emptyIntIState :: LibEnv -> LIB_NAME -> IntIState
emptyIntIState le ln =
  IntIState {
    i_libEnv = le,
    i_ln  = ln,
    elements = [],
    cComorphism = Nothing,
    prover = Nothing,
    consChecker = Nothing,
    save2file = False,
    useTheorems = False,
    script = ATPTactic_script {
                 ts_timeLimit = 20,
                 ts_extraOpts = [] },
    loadScript = False
    }



-- Create an empty command history
emptyCommandHistory :: IORef IntState -> IO (Result CommandHistory)
emptyCommandHistory st = do
  ch <- newIORef []
  ost <- readIORef st
  ff <- tryRemoveAbsolutePathComponent $ filename ost
  return $ Result [] $ Just CommandHistory { hist = ch,
                                             filePath = rmSuffix ff}

-- If an absolute path is given,
-- it tries to remove the current working directory as prefix of it.
tryRemoveAbsolutePathComponent :: String -> IO String
tryRemoveAbsolutePathComponent f
   | "/" `isPrefixOf` f = do
                           dir <- getCurrentDirectory
                           return $ fromMaybe f (stripPrefix (dir ++ "/") f)
   | otherwise        = return f

-- If at least one goal was proved and the prove is not the same as last time
-- the prove gets added, otherwise not.
addProveToHist :: CommandHistory
        -> ProofState lid sentence         -- current proofstate
        -> Maybe (G_prover, AnyComorphism) -- possible used translation
        -> [Proof_status proof_tree]       -- goals included in prove
        -> IO ()
addProveToHist ch st pcm pt
    | null $ filter wasProved pt = return ()
    | otherwise = do
                  p <- proofTreeToProve ch st pcm pt
                  addToHist ch $ ProveCommand p

-- Converts a list of proof-trees to a prove
proofTreeToProve :: CommandHistory
     -> ProofState lid sentence  -- current proofstate
     -> Maybe (G_prover, AnyComorphism) -- possible used translation
     -> [Proof_status proof_tree] -- goals included in prove
     -> IO Prove
proofTreeToProve ch st pcm pt =
  do
  -- selected prover
  let prvr = maybe (selectedProver st) (Just . getProverName .fst ) pcm
  -- selected translation
      trans = maybe Nothing (Just . snd) pcm
  -- 1. filter out the not proven goals
  -- 2. reverse the list, because the last proven goals are on top
  -- 3. convert all proof-trees to goals
  -- 4. merge goals with same used axioms
      goals = mergeGoals $ reverse $ map convertGoal $ filter wasProved pt
  -- axioms to include in prove
      allax = case theory st of
                 G_theory _ _ _ axs _ -> keys axs
      nodeName = dropName (filePath ch) $ theoryName st
  return Prove { nodeNameStr = nodeName,
                 usedProver = prvr,
                 translation = trans,
                 provenGoals = goals,
                 allAxioms = allax}

dropName :: String -> String -> String
dropName fch s = maybe s tail (stripPrefix fch s)

-- This checks wether a goal was proved or not
wasProved :: Proof_status proof_Tree -> Bool
wasProved g = case goalStatus g of
    Proved _  -> True
    _         -> False

-- Converts a proof-tree into a goal.
convertGoal :: Proof_status proof_tree -> ProvenGoal
convertGoal pt =
  ProvenGoal {name = goalName pt, axioms = usedAxioms pt, time_Limit = tLimit}
  where
     (Tactic_script scrpt) = tacticScript pt
     tLimit = maybe 20 read (parseTimeLimit $ splitOn '\n' scrpt)

-- Parses time-limit from the tactic-script of a goal.
parseTimeLimit :: [String] -> Maybe String
parseTimeLimit l =
    if null l' then Nothing else Just $ drop (length tlStr) $ last l'
    where
       l' = filter (isPrefixOf tlStr) l
       tlStr = "Time limit: "

-- Merges goals with the same used axioms into one goal.
mergeGoals :: [ProvenGoal] -> [ProvenGoal]
mergeGoals []     = []
mergeGoals (h:[]) = [h]
mergeGoals (h:t) | mergeAble h h' = mergeGoals $ merge h h':tail t
                 | otherwise      = h:mergeGoals t
                 where
                    h' = head t
                    mergeAble :: ProvenGoal -> ProvenGoal -> Bool
                    mergeAble a b = axioms a == axioms b &&
                                    time_Limit a == time_Limit b
                    merge :: ProvenGoal -> ProvenGoal -> ProvenGoal
                    merge a b = a{name = name a ++ ' ':name b}



addCommandHistoryToState :: CommandHistory -> IORef IntState -> IO (Result ())
addCommandHistoryToState ch ioSt
 = do
    ost <- readIORef ioSt
    lsch <- readIORef $ hist ch
    let z = Int_CmdHistoryDescription {
             cmdName = joinWith '\n' $ map show lsch,
             cmdDescription = [ IStateChange $ i_state ost ]
             }
        nwst = ost { i_hist = (i_hist ost) {
                                undoList = z: (undoList $ i_hist ost)}}
    writeIORef ioSt nwst
    return $ Result [] $ Just ()
