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
-- import Static.DGTranslation

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
    let gc = lookupGlobalContext ln le
        nodesList = Graph.nodes $ devGraph gc
    in  getDGLogicFromNodes nodesList emptyResult gc
  where  
    -- rekursiv translate alle nodes of DevGraph of GlobalContext
    getDGLogicFromNodes [] result _ = result
    getDGLogicFromNodes (h:r) (Res.Result mainDiags gSublogic) gcon  =  
        case fst $ match h $ devGraph gcon of
          Just (inLinks, _, nodeLab, _) ->
            -- test if all inlinks of node are homogeneous.
            case testHomogenAndGetSublogicFromEdges inLinks Nothing of
             (_, False) ->                  
                 let diag = Res.mkDiag Res.Error ((show $ dgn_name nodeLab) 
                             ++ " has more than one not homogeneous edge.") ()
                 in getDGLogicFromNodes r 
                        (Res.Result (mainDiags ++ [diag]) Nothing) gcon
             (Just sublogicOfEdges, _) ->
                 let thisSublogic = sublogicOfTh $ dgn_theory nodeLab
                 in  case gSublogic of
                       Nothing ->
                        getDGLogicFromNodes r (Res.Result mainDiags 
                            (comSublogics thisSublogic sublogicOfEdges)) gcon
                       Just oldSublogic -> 
                        getDGLogicFromNodes r (Res.Result mainDiags 
                          (comSublogicsList 
                           [oldSublogic, thisSublogic, sublogicOfEdges] 
                           Nothing)) gcon
             (Nothing, _) -> 
                 let thisSublogic = sublogicOfTh $ dgn_theory nodeLab
                 in  case gSublogic of
                       Nothing ->
                        getDGLogicFromNodes r (Res.Result mainDiags 
                                               (Just thisSublogic)) gcon
                       Just oldSublogic -> 
                        getDGLogicFromNodes r (Res.Result mainDiags 
                          (comSublogics oldSublogic thisSublogic)) gcon
          Nothing -> 
              let diag = Res.mkDiag Res.Error (show h 
                           ++ " has be not found in GlobalContext.") ()
              in getDGLogicFromNodes r (Res.Result (mainDiags ++ [diag]) 
                                           gSublogic) gcon
   
    emptyResult = Res.Result [] Nothing

testHomogenAndGetSublogicFromEdges :: 
    [(DGLinkLab, Graph.Node)] -> Maybe G_sublogics -> (Maybe G_sublogics, Bool)
testHomogenAndGetSublogicFromEdges [] result = (result, True)
testHomogenAndGetSublogicFromEdges (((DGLink gm@(GMorphism cid' lsign lmorphism)
                                                 _ _),_):r) oldSublogic 
   =
    if isHomogeneous gm then
        case oldSublogic of
          Nothing -> 
            testHomogenAndGetSublogicFromEdges r (comSublogics g_mor g_sign) 
          Just oSublogic ->
              testHomogenAndGetSublogicFromEdges r (comSublogicsList
                                          [oSublogic, g_mor, g_sign] Nothing)
     else (Nothing, False)

   where g_mor = sublogicOfMor (G_morphism (targetLogic cid') lmorphism)
         g_sign = sublogicOfSign (G_sign (sourceLogic cid') lsign)


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

comSublogicsList :: [G_sublogics] -> Maybe G_sublogics -> Maybe G_sublogics
comSublogicsList [] result = result
comSublogicsList (sl:r) oldRes = 
    case oldRes of
      Nothing -> comSublogicsList r (Just sl)
      Just old -> comSublogicsList r (comSublogics old sl)


