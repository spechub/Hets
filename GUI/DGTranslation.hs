{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (Logic)

display the logic graph
-}

module GUI.DGTranslation (getDGLogic) where

--  data structure
import Logic.Grothendieck
import Logic.Coerce
import Logic.Logic
import Logic.Comorphism

import Static.GTheory
import Static.DevGraph
import Static.PrintDevGraph

import Common.ExtSign
import Common.LibName
import Common.Result as Res

import qualified Data.Map as Map
import Data.Graph.Inductive.Graph as Graph

-- | get the maximal sublogic of a graph.
-- | each DGraph and each node will be tested, in order to find
-- | the maximal sublogic of th Graph.
-- | All edges and nodes will be searched also in the meantime, so as to test,
-- | whether the GMorphism of edges is homogeneous, and the logics of nodes are
-- | equal.
getDGLogic :: LibEnv -> Res.Result G_sublogics
getDGLogic libEnv =
    let sublogicsMap = map (getSublogicFromDGraph libEnv)
                           (Map.keys libEnv)
    in  foldr comResSublogics (Res.Result [] Nothing) sublogicsMap

getSublogicFromDGraph :: LibEnv -> LIB_NAME -> Res.Result G_sublogics
getSublogicFromDGraph le ln =
    let edgesList = labEdgesDG gc
        nodesList = labNodesDG gc
        slList1   = map testAndGetSublogicFromEdge edgesList
        slList2   = map (getSubLogicsFromNodes $ getFirstLogic nodesList)
                        nodesList
    in  foldr comResSublogics (Res.Result [] Nothing) (slList1 ++ slList2)

  where
    gc = lookupDGraph ln le

    testAndGetSublogicFromEdge :: LEdge DGLinkLab -> Res.Result G_sublogics
    testAndGetSublogicFromEdge l@(_, _,
             DGLink gm@(GMorphism cid' (ExtSign lsign _) _ lmorphism _) _ _ _)
        =
          if isHomogeneous gm then
              Result [] (comSublogics g_mor g_sign)
              else Result [Res.mkDiag Res.Error
                           ("the " ++ showLEdge l ++
                            " is not homogeneous.") () ] Nothing

         where g_mor = G_sublogics (targetLogic cid') $ minSublogic lmorphism
               g_sign = G_sublogics (sourceLogic cid') $ minSublogic lsign


    getSubLogicsFromNodes :: AnyLogic -> LNode DGNodeLab
                          -> Res.Result G_sublogics
    getSubLogicsFromNodes logic (_, lnode) =
        case dgn_theory lnode of
          th@(G_theory lid _ _ _ _) ->
              if Logic lid == logic then
                  Res.Result [] (Just $ sublogicOfTh th)
                 else Res.Result [Res.mkDiag Res.Error
                              ("the node " ++ (getDGNodeName lnode) ++
                               "  has a different logic \"" ++ (show lid) ++
                               "\" as the logic of Graph \"" ++ (show logic) ++
                               " is not homogeneous.") () ] Nothing

    getFirstLogic :: [LNode DGNodeLab] -> AnyLogic
    getFirstLogic list =
        case dgn_theory $ snd $ head list of
          G_theory lid _ _ _ _ ->
              Logic lid


comResSublogics :: Res.Result G_sublogics
                -> Res.Result G_sublogics
                -> Res.Result G_sublogics
comResSublogics (Res.Result diags1 msubl1@(Just subl1))
                    (Res.Result diags2 msubl2) =
               case msubl2 of
                 Nothing -> Res.Result (diags1 ++ diags2) msubl1
                 Just subl2 ->
                     Res.Result (diags1 ++ diags2) $ comSublogics subl1 subl2
comResSublogics (Res.Result diags1 Nothing) (Res.Result diags2 _) =
    Result (diags1 ++ diags2) Nothing

comSublogics :: G_sublogics -> G_sublogics -> Maybe G_sublogics
comSublogics (G_sublogics lid1 l1) (G_sublogics lid2 l2) =
    case coerceSublogic lid1 lid2 "coerce Sublogic" l1 of
      Just sl -> Just (G_sublogics lid2 (join sl l2))
      Nothing -> Nothing
