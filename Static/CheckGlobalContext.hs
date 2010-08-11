{- |
Module      :  $Header$
Description :  checking consistency of indices
Copyright   :  (c) Jianchun Wang, C. Maeder, Uni Bremen 2002-2007
License     :  GPLv2 or higher
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

compare indices from development graphs to the corresponding maps of
the global context
-}

module Static.CheckGlobalContext where

import Static.DevGraph
import Static.GTheory
import Logic.Grothendieck
import Logic.Comorphism

import Common.Lib.State

data Statistics = Statistics
    { zeroSign, wrongSign, rightSign :: SigId
    , zeroMor, wrongMor, rightMor :: MorId
    , zeroTh, wrongTh, rightTh :: ThId }
    deriving Show

initStat :: Statistics
initStat = Statistics
  { zeroSign = startSigId
  , wrongSign = startSigId
  , rightSign = startSigId
  , zeroMor = startMorId
  , wrongMor = startMorId
  , rightMor = startMorId
  , zeroTh = startThId
  , wrongTh = startThId
  , rightTh = startThId }

incrZeroSign :: Statistics -> Statistics
incrZeroSign s = s { zeroSign = succ $ zeroSign s }

incrWrongSign :: Statistics -> Statistics
incrWrongSign s = s { wrongSign = succ $ wrongSign s }

incrRightSign ::Statistics -> Statistics
incrRightSign s = s { rightSign = succ $ rightSign s }

incrZeroG_theory :: Statistics -> Statistics
incrZeroG_theory s = s { zeroTh = succ $ zeroTh s }

incrWrongG_theory :: Statistics -> Statistics
incrWrongG_theory s = s { wrongTh = succ $ wrongTh s }

incrRightG_theory :: Statistics -> Statistics
incrRightG_theory s = s { rightTh = succ $ rightTh s }

incrZeroGMorphism :: Statistics -> Statistics
incrZeroGMorphism s = s { zeroMor = succ $ zeroMor s }

incrWrongGMorphism :: Statistics -> Statistics
incrWrongGMorphism s = s { wrongMor = succ $ wrongMor s }

incrRightGMorphism :: Statistics -> Statistics
incrRightGMorphism s = s { rightMor = succ $ rightMor s }

checkG_theory :: G_theory -> DGraph -> State Statistics ()
checkG_theory g@(G_theory _ _ si _ ti) dgraph = do
    if si == startSigId then modify incrZeroSign
       else case lookupSigMapDG si dgraph of
          Nothing -> error "checkG_theory: Sign"
          Just signErg -> if signOf g /= signErg then modify incrWrongSign
                          else modify incrRightSign
    if ti == startThId then modify incrZeroG_theory
       else case lookupThMapDG ti dgraph of
          Nothing -> error "checkG_theory: Theory"
          Just thErg -> if g /= thErg then modify incrWrongG_theory
                        else modify incrRightG_theory

checkG_theoryInNode :: DGraph -> DGNodeLab -> State Statistics ()
checkG_theoryInNode dgraph dg = checkG_theory (dgn_theory dg) dgraph

checkG_theoryInNodes :: DGraph -> State Statistics ()
checkG_theoryInNodes dgraph =
    mapM_ (checkG_theoryInNode dgraph) $ getDGNodeLab dgraph

checkGMorphism :: GMorphism -> DGraph -> State Statistics ()
checkGMorphism g@(GMorphism cid sign si _ mi) dgraph = do
    if si == startSigId then modify incrZeroSign
       else case lookupSigMapDG si dgraph of
           Nothing -> error "checkGMorphism: Sign"
           Just signErg -> if  G_sign (sourceLogic cid) sign si /= signErg
                           then modify incrWrongSign
                           else modify incrRightSign
    if mi == startMorId then modify incrZeroGMorphism
       else case lookupMorMapDG mi dgraph of
           Nothing -> error "checkGMorphism: Morphism"
           Just morErg -> if g /= gEmbed morErg then modify incrWrongGMorphism
                          else modify incrRightGMorphism

getDGLinkLab :: DGraph -> [DGLinkLab]
getDGLinkLab dgraph = map (\ (_, _, l) -> l) $ labEdgesDG dgraph

getDGNodeLab :: DGraph -> [DGNodeLab]
getDGNodeLab dgraph = map snd $ labNodesDG dgraph

checkGMorphismInNode :: DGraph -> DGNodeLab -> State Statistics ()
checkGMorphismInNode dgraph dg = case dgn_sigma dg of
    Nothing -> return ()
    Just gmor -> checkGMorphism gmor dgraph

checkGMorphismInNodes :: DGraph -> State Statistics ()
checkGMorphismInNodes dgraph =
    mapM_ (checkGMorphismInNode dgraph) $ getDGNodeLab dgraph

checkGMorphismInEdge :: DGraph -> DGLinkLab -> State Statistics ()
checkGMorphismInEdge dgraph (DGLink {dgl_morphism = dgmor}) =
    checkGMorphism dgmor dgraph

checkGMorphismInEdges :: DGraph -> State Statistics ()
checkGMorphismInEdges dgraph =
    mapM_ (checkGMorphismInEdge dgraph) $ getDGLinkLab dgraph

checkDGraph :: DGraph -> State Statistics ()
checkDGraph dgraph = do
    checkGMorphismInNodes dgraph
    checkG_theoryInNodes dgraph
    checkGMorphismInEdges dgraph

printStatistics :: DGraph -> String
printStatistics dgraph = unlines
    [ "maxSigIndex = " ++ show (snd $ sigMapI dgraph)
    , "maxGMorphismIndex = " ++ show (snd $ morMapI dgraph)
    , "maxG_theoryIndex = " ++ show (snd $ thMapI dgraph)
    , show $ execState (checkDGraph dgraph) initStat
    ]
