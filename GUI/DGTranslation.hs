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
import Syntax.AS_Library
import Static.DevGraph
import Static.DGTranslation

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
    in  foldr comSublogics (Res.Result [] Nothing) sublogicsMap

   where comSublogics :: Res.Result G_sublogics 
                      -> Res.Result G_sublogics 
                      -> Res.Result G_sublogics
         comSublogics (Res.Result diags1 msubl1) (Res.Result diags2 msubl2) =
            case msubl2 of
              Nothing -> Res.Result (diags1 ++ diags2) msubl1
              Just subl2 -> if isProperSublogic (fromJust msubl1) subl2 
                               then Res.Result (diags1 ++ diags2) msubl2 
                               else Res.Result (diags1 ++ diags2) msubl1

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
            if testHomogen inLinks 
             then
              let thisSublogic = sublogicOfTh $ dgn_theory nodeLab
              in case gSublogic of
                   Nothing ->
                       getDGLogicFromNodes r (Res.Result mainDiags 
                                                     (Just thisSublogic)) gcon
                   Just oldSublogic -> 
                    if isProperSublogic thisSublogic oldSublogic
                     then 
                         let diag = Res.mkDiag Res.Hint (show thisSublogic 
                                          ++ " is proper sublogic of " 
                                          ++ show oldSublogic) ()
                         in  getDGLogicFromNodes r (Res.Result (mainDiags 
                                                 ++ [diag]) gSublogic) gcon
                     else let diag = Res.mkDiag Res.Hint (show thisSublogic 
                                           ++ " is not proper sublogic of " 
                                           ++ show oldSublogic) () 
                          in getDGLogicFromNodes r (Res.Result (mainDiags 
                                       ++ [diag]) (Just thisSublogic)) gcon
            else let diag = Res.mkDiag Res.Error ((show $ dgn_name nodeLab) 
                             ++ " has more than one not homogeneous edge.") ()
                 in getDGLogicFromNodes r 
                        (Res.Result (mainDiags ++ [diag]) Nothing) gcon
          Nothing -> 
              let diag = Res.mkDiag Res.Error (show h 
                           ++ " has be not found in GlobalContext.") ()
              in getDGLogicFromNodes r (Res.Result (mainDiags ++ [diag]) 
                                           gSublogic) gcon

    emptyResult = Res.Result [] Nothing

testHomogen :: [(DGLinkLab, Graph.Node)] -> Bool
testHomogen [] = True
testHomogen (((DGLink gm _ _),_):r) =
    if isHomogeneous gm then
        testHomogen r
     else False

