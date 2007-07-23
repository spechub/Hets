{- |
Module      :  $Header$
Description :  the proof status with manipulating functions
Copyright   :  (c) Jorina F. Gerken, Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ken@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

the proof status with manipulating functions
-}

module Proofs.StatusUtils
    ( lookupHistory
    , mkResultProofStatus
    , updateProofStatus
    , prepareProofStatus
    , reviseProofStatus
    , removeContraryChanges
    , isIdentityEdge
    , showChanges
    ) where

import Static.DevGraph
import Data.Graph.Inductive.Graph
import Common.DocUtils
import qualified Data.Map as Map
import Syntax.AS_Library
import Logic.Grothendieck
import Logic.Logic

{-
   proof status = (DG0,[(R1,DG1),...,(Rn,DGn)])
   DG0 is the development graph resulting from the static analysis
   Ri is a list of rules that transforms DGi-1 to DGi
   With the list of intermediate proof states, one can easily implement
    an undo operation
-}

-- -------------------------------
-- methods used in several proofs
-- -------------------------------

{- returns the history that belongs to the given library name-}
lookupHistory :: LIB_NAME -> LibEnv -> ProofHistory
lookupHistory ln = proofHistory . lookupGlobalContext ln

mkResultProofStatus :: LIB_NAME -> LibEnv -> DGraph
                    -> ([DGRule], [DGChange]) -> LibEnv
mkResultProofStatus ln ps dgraph (dgrules, dgchanges) =
  let c = lookupGlobalContext ln ps
      historyElem = (dgrules,removeContraryChanges dgchanges)
  in Map.insert ln (c { devGraph = dgraph
                      , proofHistory = historyElem : proofHistory c })
     $ prepareResultProofHistory ps

mapProofHistory :: (ProofHistory -> ProofHistory) -> LibEnv -> LibEnv
mapProofHistory f = Map.map ( \ c -> c { proofHistory = f $ proofHistory c } )

prepareResultProofHistory :: LibEnv -> LibEnv
prepareResultProofHistory = mapProofHistory (emptyHistory :)

-- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
-- prepare, revise, lookup, update on proofstatus and its components
-- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

{- prepares the all histories of the proof history of the given proofstatus -}
prepareProofStatus :: LibEnv -> LibEnv
prepareProofStatus = mapProofHistory prepareHistory

{- prepares the given history for the rule application by appending
   an empty list tuple to the front of it, if there is not already one
   with an empty change list-}
prepareHistory :: ProofHistory -> ProofHistory
prepareHistory [] = [emptyHistory]
prepareHistory history@((_,[]):_) = history
prepareHistory history = emptyHistory : history

{- revises the history of the given proofstatus -}
reviseProofStatus :: LibEnv -> LibEnv
reviseProofStatus = mapProofHistory reviseHistory

{- removes the contrary changes form the given history and adds the name
   of the proof method (TheoremHideShift) -}
reviseHistory :: ProofHistory -> ProofHistory
reviseHistory [] = []
reviseHistory ((_,changes) : history) =
  ([TheoremHideShift], removeContraryChanges changes) : history

{- updates the library environment and the proof history of the given
   proofstatus for the given library name-}
updateProofStatus :: LIB_NAME -> DGraph -> [DGChange] -> LibEnv
                  -> LibEnv
updateProofStatus ln dgraph changes =
  Map.update (\ c -> Just c
               { devGraph = dgraph
               , proofHistory = addChanges changes $ proofHistory c}) ln

{- adds the given changes to the given history -}
addChanges :: [DGChange] -> [([DGRule],[DGChange])] -> [([DGRule],[DGChange])]
addChanges changes [] = [([],changes)]
addChanges changes (hElem:history) = (fst hElem, (snd hElem)++changes):history

-- - - - - - - - - - - - - - - - - - - - - -
-- debug methods to print a list of changes
-- - - - - - - - - - - - - - - - - - - - - -

showChanges :: [DGChange] -> String
showChanges [] = ""
showChanges (change:changes) =
  case change of
    InsertEdge edge -> "InsertEdge " ++ (showEdgeChange edge)
                       ++ (showChanges changes)
    DeleteEdge edge -> "DeleteEdge " ++ (showEdgeChange edge)
                       ++ (showChanges changes)
    InsertNode node -> "InsertNode " ++ (showNodeChange node)
                       ++ (showChanges changes)
    DeleteNode node -> "DeleteNode " ++ (showNodeChange node)
                       ++ (showChanges changes)
    SetNodeLab _ (node, newLab) -> "SetNodeLab of node " ++ show node ++
                                 " with new lab: " ++ show newLab

showEdgeChange :: LEdge DGLinkLab -> String
showEdgeChange (src,tgt,edgelab) =
  " from " ++ (show src) ++ " to " ++ (show tgt)
  ++ " and of type " ++ showDoc (dgl_type edgelab) "\n\n"

showNodeChange :: LNode DGNodeLab -> String
showNodeChange (descr, nodelab) =
  (show descr) ++ " with name " ++ (show (dgn_name nodelab)) ++ "\n\n"

-- ----------------------------------------------
-- methods that keep the change list clean
-- ----------------------------------------------

removeContraryChanges :: [DGChange] -> [DGChange]
removeContraryChanges [] = []
removeContraryChanges (change:changes) =
  case contraryChange of
    Just c -> removeContraryChanges (removeChange c changes)
    Nothing -> change:(removeContraryChanges changes)
  where
    contraryChange =
      case getContraryChange change of
        Just c -> if c  `elem` changes then Just c else Nothing
        Nothing -> Nothing

getContraryChange :: DGChange -> Maybe DGChange
getContraryChange change = case change of
    InsertEdge edge -> Just $ DeleteEdge edge
    -- re-insertion of deleted edge may be useful if node has changed
    InsertNode node -> Just $ DeleteNode node
    -- re-insertion of deleted node may be useful if node has changed
    -- ... although this should be recognized ... a bit strange ...
    DeleteEdge _ -> Nothing
    DeleteNode _ -> Nothing -- Just $ InsertNode node
    SetNodeLab _ _ -> Nothing

removeChange :: DGChange -> [DGChange] -> [DGChange]
removeChange _ [] = []
removeChange c1 (c2:rest) | c1==c2 = rest
-- when a node is removed afterwards, throw away all edge operations
-- refering to that node that are encountered on the way
removeChange c1@(DeleteNode (n,_)) (c2:rest) =
  if case c2 of
     InsertEdge (n1,n2,_) -> n==n1 || n==n2
     DeleteEdge (n1,n2,_) -> n==n1 || n==n2
     _ -> False
   then removeChange c1 rest
   else c2:removeChange c1 rest
removeChange c1 (c2:rest) = c2:removeChange c1 rest

isIdentityEdge :: LEdge DGLinkLab -> LibEnv -> DGraph -> Bool
isIdentityEdge (src,tgt,edgeLab) ps dgraph =
  if isDGRef nodeLab then
    let dg = lookupDGraph (dgn_libname nodeLab) ps in
      isIdentityEdge (dgn_node nodeLab,tgt,edgeLab) ps dg
   else src == tgt &&
        dgl_morphism edgeLab == ide Grothendieck (dgn_sign nodeLab)
  where nodeLab = lab' $ safeContextDG "Proofs.EdgeUtils.isIdentityEdge"
                  dgraph src
