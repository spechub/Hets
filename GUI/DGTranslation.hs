{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@tzi.de
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
import Syntax.AS_Library
import Static.DevGraph
import Static.DGTranslation (showFromTo)

import qualified Common.Lib.Map as Map
import Common.Result as Res
import Data.Graph.Inductive.Graph as Graph
import Data.Maybe

-- | get the maximal sublogic of a graph.
-- | each GlobalContext and each node will be tested, in order to find
-- | the maximal sublogic of th Graph. 
-- | All edges will be searched also in the meantime, so as to test, whether 
-- | the GMorphism of these is homogeneous.
getDGLogic :: LibEnv -> Res.Result G_sublogics
getDGLogic libEnv = 
    let sublogicsMap = map (getSublogicFromGlobalContext libEnv) 
                           (Map.keys libEnv)
    in  foldr comResSublogics (Res.Result [] Nothing) sublogicsMap

getSublogicFromGlobalContext :: LibEnv -> LIB_NAME -> Res.Result G_sublogics
getSublogicFromGlobalContext le ln =
    let edgesList = Graph.labEdges $ devGraph gc
        nodesList = Graph.labNodes $ devGraph gc
        slList1   = map testAndGetSublogicFromEdge edgesList 
        slList2   = getDGLogicFromNodes nodesList 
    in  foldr comResSublogics (Res.Result [] Nothing) (slList1 ++ slList2) 

  where 
    gc = lookupGlobalContext ln le

    testAndGetSublogicFromEdge :: LEdge DGLinkLab -> Res.Result G_sublogics
    testAndGetSublogicFromEdge (from, to, 
                                 DGLink gm@(GMorphism cid' lsign lmorphism) _ _) 
        =
          if isHomogeneous gm then
              Result [] (comSublogics g_mor g_sign) 
              else Result [Res.mkDiag Res.Error 
                           ("the edge " ++ (showFromTo from to gc) ++
                            " is not homogeneous.") () ] Nothing 

         where g_mor = sublogicOfMor (G_morphism (targetLogic cid') lmorphism)
               g_sign = sublogicOfSign (G_sign (sourceLogic cid') lsign) 

    getDGLogicFromNodes :: [LNode DGNodeLab] -> [Res.Result G_sublogics]
    getDGLogicFromNodes nodesList =
        map getDGLogicFromNode nodesList
              
    getDGLogicFromNode :: LNode DGNodeLab -> Res.Result G_sublogics
    getDGLogicFromNode (_, lnode) =
        Res.Result [] (Just $ sublogicOfTh $ dgn_theory lnode)

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

{-
comSublogicsList :: [G_sublogics] -> Maybe G_sublogics -> Maybe G_sublogics
comSublogicsList [] result = result
comSublogicsList (sl:r) oldRes = 
    case oldRes of
      Nothing -> comSublogicsList r (Just sl)
      Just old -> comSublogicsList r (comSublogics old sl)
-}

