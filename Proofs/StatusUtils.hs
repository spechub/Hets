{- |
Module      :  $Header$
Description :  the proof status with manipulating functions
Copyright   :  (c) Jorina F. Gerken, Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

the proof status with manipulating functions
-}

module Proofs.StatusUtils
    ( lookupHistory
    , removeContraryChanges
    , isIdentityEdge
    ) where

import Static.DevGraph
import Data.Graph.Inductive.Graph
import Common.LibName
import Logic.Logic
import qualified Common.Lib.SizedList as SizedList

import Data.List

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

{- returns the history that belongs to the given library name -}
lookupHistory :: LibName -> LibEnv -> ProofHistory
lookupHistory ln = clearHist . proofHistory . lookupDGraph ln

-- clear label lock
clr :: DGNodeLab -> DGNodeLab
clr l = l { dgn_lock = Nothing }

clearLock :: DGChange -> DGChange
clearLock c = case c of
  InsertNode (n, l) -> InsertNode (n, clr l)
  DeleteNode (n, l) -> InsertNode (n, clr l)
  SetNodeLab o (n, l) -> SetNodeLab (clr o) (n, clr l)
  _ -> c

clearHist :: ProofHistory -> ProofHistory
clearHist = SizedList.map clearElem

clearElem :: HistElem -> HistElem
clearElem e = case e of
  HistElem c -> HistElem $ clearLock c
  HistGroup r h -> HistGroup r $ clearHist h

-- ----------------------------------------------
-- methods that keep the change list clean
-- ----------------------------------------------

{- | remove the contray changes out of the list if it's necessary,
     so that the list can stay clean.
-}
removeContraryChanges :: [DGChange] -> [DGChange]
removeContraryChanges cs = case cs of
  [] -> []
  c1 : r -> let recurse = c1 : removeContraryChanges r in case c1 of
    SetNodeLab oldLbl (n, _) -> let
        (r1, r2) = break (\ c2 -> case c2 of
            SetNodeLab _ (m, _) -> n == m
            DeleteNode (m, _) -> n == m
            _ -> False) r
        in case r2 of
             [] -> recurse
             c2 : r3 -> removeContraryChanges $ r1 ++ case c2 of
                 SetNodeLab _ (_, lbl) -> SetNodeLab oldLbl (n, lbl) : r3
                 DeleteNode _ -> DeleteNode (n, oldLbl) : r3
                 _ -> r2
    InsertNode (n, _) -> let
        (r1, r2) = break (\ c2 -> case c2 of
            DeleteNode (m, _) -> n == m
            _ -> False) r
        (r1a, r1b) = partition (\ c2 -> case c2 of
            SetNodeLab _ (m, _) -> n == m
            _ -> False) r1
        in case r2 of
             [] -> case reverse r1a of
                SetNodeLab _ (_, lbl) : _ ->
                    InsertNode (n, lbl) : removeContraryChanges r1b
                _ -> recurse
             _ : r3 -> removeContraryChanges $
                       filter (\ c2 -> case c2 of
                          InsertEdge (s, t, _) -> s /= n && t /= n
                          DeleteEdge (s, t, _) -> s /= n && t /= n
                          _ -> True) r1b ++ r3
    DeleteNode (n, oldLbl) -> let
        (r1, r2) = break (\ c2 -> case c2 of
            InsertNode (m, _) -> n == m
            _ -> False) r
        in case r2 of
             InsertNode (_, lbl) : r3 ->
               removeContraryChanges $ r1 ++ SetNodeLab oldLbl (n, lbl) : r3
             _ -> recurse
    InsertEdge e1 -> let
        (r1, r2) = break (\ c2 -> case c2 of
            DeleteEdge e2 -> e1 == e2
            _ -> False) r
        in case r2 of
             [] -> recurse
             _ : r3 -> removeContraryChanges $ r1 ++ r3
    DeleteEdge e1 -> let
        (r1, r2) = break (\ c2 -> case c2 of
            InsertEdge e2 -> e1 == e2
            _ -> False) r
        in case r2 of
             [] -> recurse
             _ : r3 -> removeContraryChanges $ r1 ++ r3

{- | check if the given edge is an identity edge, namely a loop
     from a node to itself with an identity morphism. -}
isIdentityEdge :: LEdge DGLinkLab -> LibEnv -> DGraph -> Bool
isIdentityEdge (src, tgt, edgeLab) ps dgraph =
  let nodeLab = labDG dgraph src
      gsig = dgn_sign nodeLab
      res = src == tgt &&
        dgl_morphism edgeLab == ide gsig
  in if isDGRef nodeLab then -- just a consistency check
    let dg = lookupDGraph (dgn_libname nodeLab) ps
        gsig2 = dgn_sign $ labDG dg $ dgn_node nodeLab
    in if gsig2 == gsig then res else error "isIdentityEdge"
  else res
