{- |
Module      :  $Header$
Description :  checking consistency of indices
Copyright   :  (c) Jianchun Wang, Uni Bremen 2002-2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  wjch868@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

compare indices from development graphs to the corresponding maps of
the global context
-}


module Static.CheckGlobalContext where

import Logic.Logic
import Static.DevGraph
import Logic.Grothendieck
import Logic.Comorphism
import Common.Result

import Data.Graph.Inductive.Graph
import qualified Data.Map as Map
import Common.Lib.State

data Statistics = Statistics
  { zeroSign, wrongSign, zeroMor, wrongMor, zeroTh, wrongTh :: Int }

initStat :: Statistics
initStat = Statistics { zeroSign = 0, wrongSign = 0, zeroMor = 0,
                        wrongMor = 0, zeroTh = 0, wrongTh = 0 } 

incrZeroSign :: Statistics -> Statistics
incrZeroSign s = s { zeroSign = zeroSign s + 1 }

incrWrongSign :: Statistics -> Statistics
incrWrongSign s = s { wrongSign = wrongSign s + 1 } 

incrZeroG_theory :: Statistics -> Statistics
incrZeroG_theory s = s { zeroTh = zeroTh s + 1 }

incrWrongG_theory :: Statistics -> Statistics
incrWrongG_theory s = s { wrongTh = wrongTh s + 1 }

incrZeroGMorphism :: Statistics -> Statistics
incrZeroGMorphism s = s { zeroMor = zeroMor s +1 }

incrWrongGMorphism :: Statistics -> Statistics
incrWrongGMorphism s = s { wrongMor = wrongMor s + 1 }

checkG_theory :: G_theory -> GlobalContext -> State Statistics ()
checkG_theory g@(G_theory lid sign si sens ti) ctxt = do 
    if si == 0 then modify incrZeroSign
       else case Map.lookup si $ sigMap ctxt of
          Nothing -> modify incrWrongSign
          Just signErg -> if signOf g /= signErg then modify incrWrongSign
                          else return ()
    if ti == 0 then modify incrZeroG_theory
       else case Map.lookup ti $ thMap ctxt of
          Nothing -> modify incrWrongG_theory
          Just thErg -> if g /= thErg then modify incrWrongG_theory
                        else return ()

checkG_theoryInNode :: GlobalContext -> DGNodeLab -> State Statistics () 
checkG_theoryInNode ctxt dg = case dg of
    DGNode {dgn_theory = dgth} -> checkG_theory dgth ctxt
    DGRef {dgn_theory = dgth} -> checkG_theory dgth ctxt

checkG_theoryInNodes :: GlobalContext -> DGraph -> [State Statistics ()]
checkG_theoryInNodes ctxt dgraph =
    map (checkG_theoryInNode ctxt) $ getDGNodeLab dgraph

checkGMorphism :: GMorphism -> GlobalContext -> State Statistics () 
checkGMorphism g@(GMorphism cid sign si mor mi) ctxt = do
    if si == 0 then modify incrZeroSign
       else case Map.lookup si $ sigMap ctxt of
           Nothing -> modify incrWrongSign
           Just signErg -> if  G_sign (sourceLogic cid) sign si /= signErg 
                           then modify incrWrongSign
                           else return ()
    if mi == 0 then modify incrZeroGMorphism
       else case Map.lookup mi $ morMap ctxt of
           Nothing -> modify incrWrongGMorphism
           Just morErg -> if g /= gEmbed morErg then modify incrWrongGMorphism
                          else return ()
   
getDGLinkLab :: DGraph -> [DGLinkLab]
getDGLinkLab dgraph = map (\(_,_,label) -> label) $ labEdges dgraph 

getDGNodeLab :: DGraph -> [DGNodeLab]
getDGNodeLab dgraph = map snd $ labNodes dgraph

checkGMorphismInNode :: GlobalContext -> DGNodeLab -> State Statistics () 
checkGMorphismInNode ctxt dg = case dg of
    DGNode {dgn_sigma = Nothing} -> modify incrWrongGMorphism
    DGNode {dgn_sigma = Just gmor} -> checkGMorphism gmor ctxt
    DGRef {dgn_sigma = Nothing} -> modify incrWrongGMorphism
    DGRef {dgn_sigma = Just gmor} -> checkGMorphism gmor ctxt

checkGMorphismInNodes :: GlobalContext -> DGraph -> [State Statistics ()]
checkGMorphismInNodes ctxt dgraph =
    map (checkGMorphismInNode ctxt) $ getDGNodeLab dgraph

checkGMorphismInEdge :: GlobalContext -> DGLinkLab -> State Statistics ()
checkGMorphismInEdge ctxt (DGLink {dgl_morphism = dgmor}) =
    checkGMorphism dgmor ctxt

checkGMorphismInEdges :: GlobalContext -> DGraph -> [State Statistics ()] 
checkGMorphismInEdges ctxt dgraph = 
    map (checkGMorphismInEdge ctxt) $ getDGLinkLab dgraph


