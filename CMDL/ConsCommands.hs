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
import Interfaces.Utils

import CMDL.DataTypes
import CMDL.Utils
import CMDL.DataTypesUtils
import CMDL.ProveConsistency
import CMDL.DgCommands

import Proofs.AbstractState
-- import Proofs.TheoremHideShift

import Static.DevGraph
import Static.GTheory

-- import Logic.Logic (conservativityCheck)
-- import Logic.Coerce (coerceSign, coerceMorphism)
-- import Logic.Grothendieck
-- import Logic.Comorphism
-- import Logic.Prover

-- import Common.Consistency
-- import Common.ExtSign
import Common.LibName
-- import Common.Result as Res
import qualified Common.OrderedMap as OMap

import Control.Concurrent
import Control.Concurrent.MVar
import System.Posix.Signals
import System.IO
import Data.Graph.Inductive.Graph
import Data.List
import Data.Char

-- Command that processes the input and applies a
-- conservativity check
cConservCheck:: String -> CMDL_State -> IO CMDL_State
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
          _ ->
           do
              return $ genMessage tmpErrs
                         (concatMap (\(s1,s2) -> s1++" : "++s2++"\n")
                                       (edgLs ++ nbEdgLs) ) nwst


-- checks conservativity for every possible node
cConservCheckAll :: CMDL_State -> IO CMDL_State
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
cConsistCheck :: CMDL_State -> IO CMDL_State
cConsistCheck state
    = case i_state $ intState state of
       Nothing -> return $ genErrorMsg "Nothing selected" state
       Just pS ->
          do
           case elements pS of
            [] -> return $ genErrorMsg "Nothing selected" state
            ls ->
             do
              --create initial mVars to comunicate
              mlbEnv <- newMVar $ i_libEnv pS
              mSt    <- newMVar Nothing
              mThr   <- newMVar Nothing
              mW     <- newEmptyMVar
              -- fork
              thrID <- forkIO(consCheckLoop mlbEnv mThr mSt mW pS ls)
              -- install the handler that waits for SIG_INT
              installHandler sigINT (Catch $
                       sigIntHandler mThr mlbEnv mSt thrID mW (i_ln pS)
                                    ) Nothing
              -- block and wait for answers
              answ <- takeMVar mW
              let nwpS = pS {
                               i_libEnv = answ
                              }
              let nwls = concatMap (\(Element _ x) ->
                                                   selectANode x nwpS) ls
                  hst = concatMap(\(Element stt x) ->
                                     (AxiomsChange (includedAxioms stt) x):
                                     (GoalsChange (selectedGoals stt) x):
                                        []) ls
              return $ add2hist [(DgCommandChange $ i_ln nwpS),
                                 (ListChange hst)] $
                          state {
                            intState = (intState state) {
                               i_state = Just $ pS {
                                            elements = nwls } }
                             }

-- applies consistency check to all possible input
cConsistCheckAll :: CMDL_State -> IO CMDL_State
cConsistCheckAll state
   = case i_state $ intState state of
      Nothing -> return $ genErrorMsg "Nothing selected" state
      Just pS ->
        do
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
                     LibEnv -> LIB_NAME -> IO ([(String,String)], LibEnv)
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
   allEds <- applyEdgeConservativity le libname edgtm [] lsN
   return allEds


applyEdgeConservativity:: LibEnv -> LIB_NAME -> [(LEdge DGLinkLab,Bool)] ->
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
      case vl of
       True ->
        do
         (str,nwLe,_) <- checkConservativityEdge False (x,y,edgLab) le ln
         let nm = (nameOf x lsN) ++ arrowLink edgLab ++ (nameOf y lsN)
         applyEdgeConservativity nwLe ln l ((nm, str) : acc) lsN
       False ->
        do
         (str,nwLe,_) <- checkConservativityEdge False (x,y,edgLab) le ln
         let nm = nameOf x lsN ++ arrowLink edgLab
                  ++ show (getInt $ dgl_id edgLab)
                  ++ arrowLink edgLab ++ nameOf y lsN
         applyEdgeConservativity nwLe ln l ((nm, str) : acc) lsN
