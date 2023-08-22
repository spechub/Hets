{- |
Module      :  ./Common/AutoProofUtils.hs
Description :  Utils for automatic proving procedure of multiple nodes
Copyright   :  (c) Simon Ulbricht, Uni Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  tekknix@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

This module provides sturctures and methods for the automatic proofs module.
-}

module Common.AutoProofUtils where

import Common.GtkGoal

import Data.Maybe
import Data.Graph.Inductive.Graph (LNode)
import Data.List
import Data.Ord (comparing)

import Logic.Grothendieck

import Static.DevGraph
import Static.GTheory

-- | stores each node to be considered along with some further infomation
data FNode = FNode { name :: String
                   , node :: LNode DGNodeLab
                   , sublogic :: G_sublogics
                   , goals :: [String]
                     {- after proving, a new GTheory with the new Proofstatus
                     is computed -}
                   , results :: G_theory }

{- | mostly for the purpose of proper display, the resulting G_theory of each
FNode can be converted into a list of Goals. -}
toGtkGoals :: FNode -> [Goal]
toGtkGoals fn = map toGtkGoal . filter ((`elem` goals fn) . fst) . getThGoals
  $ results fn

{- | as a Prefix for display purpose, the ratio of proven and total goals
is shown -}
goalsToPrefix :: [Goal] -> String
goalsToPrefix gs = let p = length $ filter (\ g -> gStatus g == GProved) gs
                   in "[" ++ show p ++ "/" ++ show (length gs) ++ "] "

{- | Displays every goal of a Node with a prefix showing the status and the
goal name. -}
showStatus :: FNode -> String
showStatus fn = intercalate "\n" . map (\ g -> statusToPrefix
                 (gStatus g) ++ show (gName g)) $ toGtkGoals fn

-- | Get a markup string containing name and color
instance Show FNode where
  show fn = let gs = toGtkGoals fn
                gmin = gStatus $ minimum gs
            in
    "<span color=\"" ++ statusToColor gmin ++ "\">"
     ++ goalsToPrefix gs ++ name fn ++ "</span>"

instance Eq FNode where
  (==) f1 f2 = compare f1 f2 == EQ

{- | for comparison, the goal status of each node is considered. only with
equal goal status, nodes are sorted by name. -}
instance Ord FNode where
  compare = let gmin f = (minimum $ toGtkGoals f, name f)
            in comparing gmin

{- | gets all Nodes from the DGraph as input and creates a list of FNodes only
containing Nodes to be considered.
The results status field is initialised with the nodes local theory -}
initFNodes :: [LNode DGNodeLab] -> [FNode]
initFNodes = foldr (\ n@(_, l) t -> case globalTheory l of
                      Nothing -> t
                      Just gt ->
                        let gt' = dgn_theory l
                            gs = map fst $ getThGoals gt'
                        in if null gs then t else
                        FNode (getDGNodeName l) n (sublogicOfTh gt) gs gt' : t
              ) []

-- | returns True if a node has not been proved jet
unchecked :: FNode -> Bool
unchecked fn = all (isNothing . snd) . getThGoals $ results fn

-- | returns True if at least one goal has been timed out
timedout :: FNode -> Bool
timedout fn = any (\ a -> gStatus a == GTimeout) $ toGtkGoals fn

-- | returns True only if every goal has been proved
allProved :: FNode -> Bool
allProved fn = all (\ a -> gStatus a == GProved) $ toGtkGoals fn
