{- |
Module      :  $Header$
Description :  conservativity proof rule for development graphs
Copyright   :  (c) Markus Gross, DFKI 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  mgross@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Logic)

conservativity proof rule for development graphs
   Follows Sect. IV:4.4.2 of the CASL Reference Manual.
-}

module Proofs.Conservativity
    ( conservativity
    ) where

{-import Logic.Logic
import Logic.Prover
import Logic.ExtSign
import Logic.Grothendieck
import Static.GTheory
import Static.ArchDiagram-}
import Static.DevGraph

import Proofs.EdgeUtils

{-import Common.Amalgamate
import Common.Lib.Graph as Tree
import Common.Result-}
import Common.LibName

import Data.Graph.Inductive.Graph as Graph
import qualified Data.Map as Map
import Data.List (nub, nubBy)
import Data.Maybe (fromJust)
--import Control.Monad

------------------------------------------------
-- Conservativity rules
------------------------------------------------

{- A pair is defined as:

(e1, e2)

n ---- e2 ----> n
|
|
e1
|
|
v
n

-}
type Pair = (LEdge DGLinkLab, LEdge DGLinkLab)

{- A quad is defined as:

((e1, e2), (e3, e4))

n ---- e2 ----> n
|               |
|               |
e1              e4
|               |
|               |
v               v
n ---- e3 ----> n

-}
type Quad = (Pair, Pair)

-- Main function, calls all rules.
conservativity :: LIB_NAME -> LibEnv -> LibEnv
conservativity = Map.adjust (shift . freeIsMono)

-- Shift-Rule.
-- First a list of edge pairs with the same source node is generated.
-- Then all pairs are positioned correctly. All pairs which have
-- one edge with a cons value are kept.
-- A list of quads (pair, pair) is generated. Each input pair is combined with
-- another pair, which has the same target and where the edges have the same
-- source nodes. (See type Quad for a picture.)
-- The target node of the quads must be isolated and the quad has to be
-- amalgamable.
-- Afterwards the quad is positioned correctly and the edges are updated.
shift :: DGraph -> DGraph
shift dg = changesDGH dg changes
  --error $ unlines $ intersperse "\n##\n" $
  --        map (\ (x,y) -> showPair x ++ "\n" ++ showPair y) quads
  where
    edgs = filter (liftE isGlobalEdge) $ labEdgesDG dg
    globThmEdges = filter (liftE isGlobalThm) edgs
    consEdgs = [ e | e <-globThmEdges, getConservativity e > None ]
    pairs1 = nubBy nubPair [ (e1, e2) | e1@(s1,t1,_)<-consEdgs,
                                        e2@(s2,t2,_)<-globThmEdges,
                                        e1 /= e2, s1 == s2, t1 /= s1, t2 /= s2 ]
    pairs2 = nubBy nubPair [ (e3, e4) | e3@(_,t3,_)<-edgs, e4@(_,t4,_)<-edgs,
                                        e3 /= e4 && t3 == t4 ]
    quads = filter (isAmalgamable dg) $
            filter (isolated edgs . snd) $ map posQuad
            [ ((e1, e2), (e3, e4)) | (e1@(_,t1,_), e2@(_,t2,_))<-pairs1,
                                     (e3@(s3,_,_), e4@(s4,_,_))<-pairs2,
                                     ((t1 == s3 && t2 == s4) ||
                                      (t1 == s4 && t2 == s3)) ]
    changes = concatMap process quads
    -- Updates the e4 edge with the cons value from the e1 edge.
    -- The quads have to be positioned correctly before using this function.
    process :: Quad -> [DGChange]
    process ((e1, _), (_, e4@(s4, t4, l4))) =
      let cons = getConservativity e1
       in [ DeleteEdge e4, InsertEdge (s4, t4, l4 {
              dgl_type = case dgl_type l4 of
                           ScopedLink sc dl cs -> ScopedLink sc dl (case cs of
                              ConsStatus co pc tl -> ConsStatus (max cons co)
                                                                pc tl)
                           t -> t
            , dgl_origin = DGLinkProof
            , dgl_id = defaultEdgeId
          })]

-- Checks if a quad is amalgamable.
isAmalgamable :: DGraph -> Quad -> Bool
isAmalgamable _ _ = True
{-isAmalgamable dg ((e1@(s1,_,_), e2), (e3@(s3,t3,l3), e4@(s4,t4,l4))) =
  case resultToMaybe $
       ensures_amalgamability lid ([Sharing], diag, sink, Graph.empty) of
    Just Amalgamates -> True
    _                -> False
  where
    sink = case resultToMaybe $ homogeniseSink lid
                [(s3, dgl_morphism l3), (s4, dgl_morphism l4)] of
             Just s -> s
             _      -> []
    sig = cod $ snd $ head sink
    --lid :: StaticAnalysis lid
    --  basic_spec sentence symb_items symb_map_items
    --  sign morphism symbol raw_symbol => lid
    lid :: Logic lid sublogics
           basic_spec sentence symb_items symb_map_items
           sign morphism symbol raw_symbol proof_tree => lid
    lid = case sig of
            G_sign llid _ _ -> llid
    diag = Graph.empty
    --diag = resultToMaybe $
    --       homogeniseDiagram lid d-}

-- Checks wether a pair is duplicate.
nubPair :: Pair -> Pair -> Bool
nubPair (e1, e2) (e3, e4) = (e1 == e3 && e2 == e4) || (e1 == e4) && (e2 == e3)

-- Positions a quad so that the e4 edge is the one whose source node is the
-- target node of e2. Also checks if the e4 has no conservativity value.
posQuad :: Quad -> Quad
posQuad q@((e1@(_,t1,_), e2@(_,t2,_)), (e3@(s3,_,_), e4))
  | s3 == t1  = q
  | s3 == t2  = ((e1, e2), (e4, e3))
  | otherwise = error "Proofs.Conservativity.posQuad"

-- Checks wether the node of the pair is isolated.
-- Both edges of the pair have the same target node.
isolated :: [LEdge DGLinkLab] -> Pair -> Bool
isolated edgs (e1@(_,t1,_), e2) = not $ any
  (\ x@(_,t,_) -> x /= e1 && x /= e2 && t == t1 ) edgs

-- Displays the node ids of an edge pair.
{-showPair :: Pair -> String
showPair ((s1,t1,_), (s2,t2,_)) = show s1 ++ " -> " ++ show t1 ++ " && " ++
                                  show s2 ++ " -> " ++ show t2-}

-- First get all free links in the graph. Then all cons links.
-- When the free and cons link point to the same node, the cons link is upgraded
-- to mono.
freeIsMono :: DGraph -> DGraph
freeIsMono dg = changesDGH dg changes
  where
    edgs = labEdgesDG dg
    free = filter (liftE isFreeEdge) edgs
    cons = [ e | e<-edgs, liftE isGlobalThm e, getConservativity e == Cons ]
    mono = nub [ c | c@(_, ct, _)<-cons, (_, ft, _)<-free, ct == ft ]
    changes = concatMap process mono
    process :: LEdge DGLinkLab -> [DGChange]
    process m@(s, t, l) = [ DeleteEdge m, InsertEdge (s, t, l {
         dgl_type = case dgl_type l of
                      ScopedLink sc dl cs -> ScopedLink sc dl (case cs of
                              ConsStatus _ pc tl -> ConsStatus Mono pc tl)
                      tp -> tp
       , dgl_origin = DGLinkProof
       , dgl_id = defaultEdgeId
      }) ]

--monoIsFree
