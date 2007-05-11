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

import Static.DevGraph
import Logic.Grothendieck
import Logic.Comorphism

import Data.Graph.Inductive.Graph
import qualified Data.Map as Map
import Common.Lib.State

data Statistics = Statistics
    { zeroSign, wrongSign, rightSign,
      zeroMor, wrongMor, rightMor,
      zeroTh, wrongTh, rightTh :: Int } 
    deriving (Show)

initStat :: Statistics
initStat = Statistics { zeroSign = 0, wrongSign = 0, rightSign = 0, 
                        zeroMor = 0, wrongMor = 0, rightMor = 0,
                        zeroTh = 0, wrongTh = 0, rightTh = 0} 

incrZeroSign :: Statistics -> Statistics
incrZeroSign s = s { zeroSign = zeroSign s + 1 }

incrWrongSign :: Statistics -> Statistics
incrWrongSign s = s { wrongSign = wrongSign s + 1 } 

incrRightSign ::Statistics -> Statistics 
incrRightSign s = s { rightSign = rightSign s + 1 }

incrZeroG_theory :: Statistics -> Statistics
incrZeroG_theory s = s { zeroTh = zeroTh s + 1 }

incrWrongG_theory :: Statistics -> Statistics
incrWrongG_theory s = s { wrongTh = wrongTh s + 1 }

incrRightG_theory :: Statistics -> Statistics
incrRightG_theory s = s { rightTh = rightTh s + 1 } 

incrZeroGMorphism :: Statistics -> Statistics
incrZeroGMorphism s = s { zeroMor = zeroMor s +1 }

incrWrongGMorphism :: Statistics -> Statistics
incrWrongGMorphism s = s { wrongMor = wrongMor s + 1 }

incrRightGMorphism :: Statistics -> Statistics
incrRightGMorphism s = s { rightMor = rightMor s + 1 }

checkG_theory :: G_theory -> GlobalContext -> State Statistics ()
checkG_theory g@(G_theory _ _ si _ ti) ctxt = do 
    if si == 0 then modify incrZeroSign
       else case Map.lookup si $ sigMap ctxt of
          Nothing -> error "checkG_theory: Sign"
          Just signErg -> if signOf g /= signErg then modify incrWrongSign
                          else modify incrRightSign
    if ti == 0 then modify incrZeroG_theory
       else case Map.lookup ti $ thMap ctxt of
          Nothing -> error "checkG_theory: Theory"
          Just thErg -> if g /= thErg then modify incrWrongG_theory
                        else modify incrRightG_theory

checkG_theoryInNode :: GlobalContext -> DGNodeLab -> State Statistics () 
checkG_theoryInNode ctxt dg = checkG_theory (dgn_theory dg) ctxt

checkG_theoryInNodes :: GlobalContext -> DGraph -> State Statistics ()
checkG_theoryInNodes ctxt dgraph =
    mapM_ (checkG_theoryInNode ctxt) $ getDGNodeLab dgraph

checkGMorphism :: GMorphism -> GlobalContext -> State Statistics () 
checkGMorphism g@(GMorphism cid sign si _ mi) ctxt = do
    if si == 0 then modify incrZeroSign
       else case Map.lookup si $ sigMap ctxt of
           Nothing -> error "checkGMorphism: Sign"
           Just signErg -> if  G_sign (sourceLogic cid) sign si /= signErg 
                           then modify incrWrongSign
                           else modify incrRightSign
    if mi == 0 then modify incrZeroGMorphism
       else case Map.lookup mi $ morMap ctxt of
           Nothing -> error "checkGMorphism: Morphism"
           Just morErg -> if g /= gEmbed morErg then modify incrWrongGMorphism
                          else modify incrRightGMorphism
   
getDGLinkLab :: DGraph -> [DGLinkLab]
getDGLinkLab dgraph = map (\(_,_,label) -> label) $ labEdges dgraph 

getDGNodeLab :: DGraph -> [DGNodeLab]
getDGNodeLab dgraph = map snd $ labNodes dgraph

checkGMorphismInNode :: GlobalContext -> DGNodeLab -> State Statistics () 
checkGMorphismInNode ctxt dg = case dgn_sigma dg of
    Nothing -> return ()
    Just gmor -> checkGMorphism gmor ctxt

checkGMorphismInNodes :: GlobalContext -> DGraph -> State Statistics ()
checkGMorphismInNodes ctxt dgraph =
    mapM_ (checkGMorphismInNode ctxt) $ getDGNodeLab dgraph

checkGMorphismInEdge :: GlobalContext -> DGLinkLab -> State Statistics ()
checkGMorphismInEdge ctxt (DGLink {dgl_morphism = dgmor}) =
    checkGMorphism dgmor ctxt

checkGMorphismInEdges :: GlobalContext -> DGraph -> State Statistics () 
checkGMorphismInEdges ctxt dgraph = 
    mapM_ (checkGMorphismInEdge ctxt) $ getDGLinkLab dgraph

checkGlobalContext :: GlobalContext -> State Statistics ()
checkGlobalContext ctxt = do
    checkGMorphismInNodes ctxt $ devGraph ctxt
    checkG_theoryInNodes ctxt $ devGraph ctxt
    checkGMorphismInEdges ctxt $ devGraph ctxt

printStatistics :: GlobalContext -> String
printStatistics ctxt = unlines 
    [ "maxSigIndex = " ++ show (snd $ sigMapI ctxt)
    , "maxGMorphismIndex = " ++ show (snd $ morMapI ctxt)
    , "maxG_theoryIndex = " ++ show (snd $ thMapI ctxt)
    , show $ execState (checkGlobalContext ctxt) initStat
    ]
