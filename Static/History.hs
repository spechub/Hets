{- |
Module      :  $Header$
Description :  history treatment for development graphs
Copyright   :  (c) Christian Maeder, DFKI GmbH 2009
License     :  GPLv2 or higher
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

functions to keep the history entries in sync with the actual graph changes
-}

module Static.History where

import Static.DevGraph

import qualified Common.Lib.SizedList as SizedList

import Data.Graph.Inductive.Graph as Graph
import Data.List

-- | add a history item to current history.
addToProofHistoryDG :: HistElem -> DGraph -> DGraph
addToProofHistoryDG x dg =
  dg { proofHistory = SizedList.cons x $ proofHistory dg }

-- | get the old history and the new offset
splitHistory :: DGraph -> DGraph -> (ProofHistory, ProofHistory)
splitHistory oldGraph newGraph = let
  oldHist = proofHistory oldGraph
  newHist = proofHistory newGraph
  diff = SizedList.take (SizedList.size newHist - SizedList.size oldHist)
         newHist
  in (oldHist, diff)

-- | reverse the history list
reverseHistory :: SizedList.SizedList HistElem -> SizedList.SizedList HistElem
reverseHistory = SizedList.reverse . SizedList.map
  (\ e -> case e of
     HistElem _ -> e
     HistGroup r l -> HistGroup r $ reverseHistory l)

-- | group pushd changes, leave history of old graph unchanged
groupHistory :: DGraph -> DGRule -> DGraph -> DGraph
groupHistory oldGraph rule newGraph = let
  (oldHist, diff) = splitHistory oldGraph newGraph
  in if SizedList.null diff then newGraph else
     newGraph { proofHistory = SizedList.cons (HistGroup rule diff) oldHist }

-- | get most recent step
getLastHistElem :: DGraph -> HistElem
getLastHistElem dg = let hist = proofHistory dg in
  if SizedList.null hist then error "Static.DevGraph.getHistElem"
  else SizedList.head hist

-- | get most recent change
getLastChange :: DGraph -> DGChange
getLastChange dg = case getLastHistElem dg of
  HistElem c -> c
  HistGroup _ _ -> error "Static.DevGraph.getLastChange"

-- | negate change
negateChange :: DGChange -> DGChange
negateChange change = case change of
      InsertNode x -> DeleteNode x
      DeleteNode x -> InsertNode x
      InsertEdge x -> DeleteEdge x
      DeleteEdge x -> InsertEdge x
      SetNodeLab old (node, new) -> SetNodeLab new (node, old)

flatHistory :: SizedList.SizedList HistElem -> [DGChange]
flatHistory h = if SizedList.null h then [] else
  (case SizedList.head h of
    HistElem c -> [c]
    HistGroup _ l -> flatHistory l) ++ flatHistory (SizedList.tail h)

undoHistStep :: DGraph -> (DGraph, [DGChange])
undoHistStep dg = let h = proofHistory dg in
  if SizedList.null h then (dg, []) else let
  he = SizedList.head h
  (ndg, cs) = case he of
    HistElem c -> let (dg2, nc) = updateDGOnly dg $ negateChange c in
       (dg2 { proofHistory = SizedList.tail h }, [nc])
    HistGroup _ l -> let
     (dg2, ncs) = mapAccumL (\ g _ -> undoHistStep g)
        dg { proofHistory = SizedList.append l $ SizedList.tail h }
        $ SizedList.toList l
     in (dg2, concat ncs)
  in (ndg { redoHistory = SizedList.cons he $ redoHistory dg }, cs)

redoHistStep :: DGraph -> (DGraph, [DGChange])
redoHistStep dg = let h = redoHistory dg in
  if SizedList.null h then (dg, []) else
      let he = SizedList.head h
          cs = reverse $ flatHistory $ SizedList.singleton $ he
          (ndg, ncs) = updateDGAndChanges dg cs
      in (ndg { proofHistory = SizedList.cons he $ proofHistory dg
              , redoHistory = SizedList.tail h }, ncs)

-- | apply the reversed changes to the graph and add them to the history
applyProofHistory :: SizedList.SizedList HistElem -> DGraph -> DGraph
applyProofHistory l = applyReverseHistory $ reverseHistory l

applyReverseHistory :: SizedList.SizedList HistElem -> DGraph -> DGraph
applyReverseHistory l dg = if SizedList.null l then dg else
  applyReverseHistory (SizedList.tail l) $ case SizedList.head l of
    HistElem c -> changeDGH dg c
    HistGroup r h -> let dg2 = applyReverseHistory h dg in
      groupHistory dg r dg2

-- | change the given DGraph with a list of changes
changesDGH :: DGraph -> [DGChange] -> DGraph
changesDGH = foldl' changeDGH

-- | toggle the pending flag of the input edges
togglePending :: DGraph -> [LEdge DGLinkLab] -> DGraph
togglePending dg = changesDGH dg . concatMap
  (\ e@(s, t, l) ->
       [DeleteEdge e, InsertEdge
        (s, t, l { dglPending = not (dglPending l)})])

-- | forget redo stack
clearRedo :: DGraph -> DGraph
clearRedo g = g { redoHistory = SizedList.empty }

-- | change the given DGraph and the history with the given DGChange.
changeDGH :: DGraph -> DGChange -> DGraph
changeDGH g c = let (ng, nc) = updateDGOnly g c in
  addToProofHistoryDG (HistElem nc) $ clearRedo ng

-- | change the given DGraph with a list of DGChange
updateDGAndChanges :: DGraph -> [DGChange] -> (DGraph, [DGChange])
updateDGAndChanges = mapAccumL updateDGOnly

{- | change the given DGraph with given DGChange and return a new DGraph and
     the processed DGChange as well. -}
updateDGOnly :: DGraph -> DGChange -> (DGraph, DGChange)
updateDGOnly g c =
  case c of
    InsertNode n -> (updRefInfo n $ insLNodeDG n g, InsertNode n)
    DeleteNode n -> (delLNodeDG n g, DeleteNode n)
    InsertEdge e -> let (newEdge, ng) = insLEdgeDG e g in
      (ng, InsertEdge newEdge)
    DeleteEdge e -> (delLEdgeDG e g, DeleteEdge e)
    SetNodeLab _ n -> let (newG, o) = labelNodeDG n g in
      (updRefInfo n $ newG, SetNodeLab o n)

updRefInfo :: LNode DGNodeLab -> DGraph -> DGraph
updRefInfo (n, lbl) = addToRefNodesDG n $ nodeInfo lbl
