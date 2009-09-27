{- |
Module      :$Header$
Description : CMDL interface commands
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

CMDL.ConsCommands contains all commands
related to consistency\/conservativity checks

-}

module CMDL.ConsCommands
       (
         cConservCheck
       , cConservCheckAll
       , cConsistCheck
       , cConsistCheckAll
       ) where


import Interfaces.DataTypes
import Interfaces.Utils(checkConservativityEdge, checkConservativityNode,
                        getAllEdges)

import CMDL.DataTypes(CmdlState(intState))
import CMDL.DataTypesUtils(getAllNodes, add2hist, genErrorMsg, genMessage)
import CMDL.Utils(arrowLink, decomposeIntoGoals, prettyPrintErrList)
import CMDL.ProveCommands(cDoLoop)

import Proofs.AbstractState(ProofState(..))

import Static.DevGraph
import Static.GTheory(G_theory(G_theory))

import Common.Consistency
import Common.LibName(LibName)
import qualified Common.OrderedMap as OMap

import System.IO(IO)
import Data.Graph.Inductive.Graph(LNode, LEdge)
import Data.Char(String)
import Data.List((++), map, groupBy, find, sortBy, concatMap)

-- Command that processes the input and applies a
-- conservativity check
cConservCheck:: String -> CmdlState -> IO CmdlState
cConservCheck input state =
  case i_state $ intState state of
   Nothing ->
     return $ genErrorMsg "No library loaded" state
   Just dgState -> do
     let (_,edg,nbEdg,errs) = decomposeIntoGoals input
         tmpErrs = prettyPrintErrList errs
     case (edg,nbEdg) of
      ([],[]) ->
        return $ genErrorMsg( tmpErrs++"No edges in input string\n") state
      (_,_) ->
        do
         let lsNodes = getAllNodes dgState
             lsEdges = getAllEdges dgState
         (allList,nle) <- conservativityList lsNodes lsEdges
                                  (i_libEnv dgState) (i_ln dgState)
         let edgLs = concatMap (\x -> case find (
                                        \(s1,_) -> s1 == x) allList of
                                       Nothing -> []
                                       Just (s1,s2) -> [(s1,s2)]) edg
             nbEdgLs = concatMap (\x -> case find (
                                        \(s1,_) -> s1 == x) allList of
                                       Nothing -> []
                                       Just (s1,s2) -> [(s1,s2)]) nbEdg
             nwst = state {
                     intState = (intState state) {
                      i_state = Just dgState {
                                       i_libEnv = nle} } }
         case edgLs++nbEdgLs of
          [] -> return $ genErrorMsg (tmpErrs ++ "No edge in input string\n")
                                                             nwst
          _ -> return $ genMessage tmpErrs
                         (concatMap (\(s1,s2) -> s1++" : "++s2++"\n")
                                       (edgLs ++ nbEdgLs) ) nwst


-- checks conservativity for every possible node
cConservCheckAll :: CmdlState -> IO CmdlState
cConservCheckAll state =
   case i_state $ intState state of
    Nothing ->
              return $ genErrorMsg "No library loaded" state
    Just dgState ->
     do
      (resTxt,nle) <- conservativityList (getAllNodes dgState)
                                   (getAllEdges dgState)
                                   (i_libEnv dgState)
                                   (i_ln dgState)
      let nwst = state  { intState = (intState state) {
                            i_state = Just dgState { i_libEnv = nle } } }
      return $ genMessage []
                (concatMap (\(s1,s2) -> s1++" : "++s2++"\n") resTxt)  nwst


-- applies consistency check to the input
cConsistCheck :: CmdlState -> IO CmdlState
cConsistCheck = cDoLoop False

-- applies consistency check to all possible input
cConsistCheckAll :: CmdlState -> IO CmdlState
cConsistCheckAll state
   = case i_state $ intState state of
      Nothing -> return $ genErrorMsg "Nothing selected" state
      Just pS ->
         case elements pS of
          [] -> return $ genErrorMsg "Nothing selected" state
          ls ->
            do
             let ls' = map (\(Element st nb) ->
                               case theory st of
                                G_theory _ _ _ aMap _ ->
                                 Element
                                  (st {
                                     selectedGoals = OMap.keys $
                                                       goalMap st,
                                     includedAxioms = OMap.keys aMap,
                                     includedTheorems = OMap.keys $
                                                         goalMap st
                                     }) nb ) ls
             let nwSt = add2hist [ListChange [NodesChange $ elements pS]] $
                          state {
                           intState = (intState state) {
                              i_state = Just $ pS {
                                                  elements = ls' } } }
             cConsistCheck nwSt


-- applies conservativity check to a given list
conservativityList:: [LNode DGNodeLab] ->
                     [LEdge DGLinkLab] ->
                     LibEnv -> LibName -> IO ([(String,String)], LibEnv)
conservativityList lsN lsE le libname
 =
  do
   let
    ordFn x y = let (x1,x2,_) = x
                    (y1,y2,_) = y
                in if (x1,x2) > (y1,y2) then GT
                   else if (x1,x2) < (y1,y2) then LT
                        else EQ
  -- sorted and grouped list of edges
    edgs = groupBy ( \(x1,x2,_) (y1,y2,_)-> (x1,x2)==(y1,y2)) $
           sortBy ordFn lsE
    edgtm = concatMap (\l -> case l of
                              [(x,y,edgLab)] ->[((x,y,edgLab),True)]
                              _ -> map (\(x,y,edgLab) -> ((x,y,edgLab),
                                                                False)) l)
                                                  edgs
   (acc, libEnv') <- applyEdgeConservativity le libname edgtm [] lsN
   applyNodeConservativity libEnv' libname
       [ n | n<-lsN, getNodeConservativity n > None ] acc

applyNodeConservativity :: LibEnv -> LibName -> [LNode DGNodeLab]
                        -> [(String, String)] -> IO ([(String, String)], LibEnv)
applyNodeConservativity libEnv ln nds acc =
  case nds of
    []            -> return (acc, libEnv)
    n@(_,nlab):ns -> do
                       (str,nwLe,_) <- checkConservativityNode False n libEnv ln
                       applyNodeConservativity nwLe ln ns
                         ((showName $ dgn_name nlab, str):acc)

applyEdgeConservativity:: LibEnv -> LibName -> [(LEdge DGLinkLab,Bool)] ->
                          [(String, String)] -> [LNode DGNodeLab] ->
                          IO ([(String, String)], LibEnv)
applyEdgeConservativity le ln ls acc lsN
 =
  do
   let nameOf x lls = case find(\(nb,_)-> nb==x) lls of
                      Nothing -> "Unknown node"
                      Just (_,nlab) -> showName $ dgn_name nlab
   case ls of
    [] -> return (acc,le)
    ((x,y,edgLab),vl):l ->
      if vl
       then
        do
         (str,nwLe,_) <- checkConservativityEdge False (x,y,edgLab) le ln
         let nm = nameOf x lsN ++ arrowLink edgLab ++ nameOf y lsN
         applyEdgeConservativity nwLe ln l ((nm, str) : acc) lsN
       else
        do
         (str,nwLe,_) <- checkConservativityEdge False (x,y,edgLab) le ln
         let nm = nameOf x lsN ++ arrowLink edgLab
                  ++ showEdgeId (dgl_id edgLab)
                  ++ arrowLink edgLab ++ nameOf y lsN
         applyEdgeConservativity nwLe ln l ((nm, str) : acc) lsN
