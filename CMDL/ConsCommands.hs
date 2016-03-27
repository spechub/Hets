{- |
Module      :./CMDL/ConsCommands.hs
Description : CMDL interface commands
Copyright   : uni-bremen and DFKI
License     : GPLv2 or higher, see LICENSE.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

CMDL.ConsCommands contains all commands
related to consistency\/conservativity checks

-}

module CMDL.ConsCommands
  ( cConservCheck
  , cConservCheckAll
  , cConsistCheck
  , cConsistCheckAll
  ) where

import Interfaces.DataTypes
import Interfaces.Utils

import CMDL.DataTypes (CmdlState (intState), ProveCmdType (..))
import CMDL.DataTypesUtils
import CMDL.Utils
import CMDL.ProveCommands (cDoLoop)

import Proofs.AbstractState (resetSelection)

import Static.DevGraph
import Static.DgUtils

import Common.Consistency
import Common.LibName (LibName)

import Data.Graph.Inductive.Graph (LNode, LEdge)
import Data.List

flatConsRes :: [(String, String)] -> String
flatConsRes = intercalate "\n" . map (\ (s1, s2) -> s1 ++ " : " ++ s2)
  . reverse

{- Command that processes the input and applies a
conservativity check -}
cConservCheck :: String -> CmdlState -> IO CmdlState
cConservCheck input state =
  case i_state $ intState state of
   Nothing ->
     return $ genMsgAndCode "No library loaded" 1 state
   Just dgState -> do
     let (nds, edg, nbEdg, errs) = decomposeIntoGoals input
         tmpErrs = prettyPrintErrList errs
     case (nds, edg, nbEdg) of
      ([], [], []) ->
        return $ genMsgAndCode (tmpErrs ++ "nothing to check\n") 1 state
      _ ->
        do
         let lsNodes = getAllNodes dgState
             lsEdges = getAllEdges dgState
             (errs', listNodes) = obtainNodeList nds lsNodes
             (errs'', listEdges) = obtainEdgeList edg nbEdg lsNodes lsEdges
             tmpErrs' = tmpErrs ++ prettyPrintErrList errs'
             tmpErrs'' = tmpErrs' ++ prettyPrintErrList errs''
         (allList, nle) <- conservativityList lsNodes listNodes listEdges
                                  (i_libEnv dgState) (i_ln dgState)
         return $ genMessage tmpErrs'' (flatConsRes allList)
           state { intState = (intState state)
                   { i_state = Just dgState {i_libEnv = nle} } }

-- checks conservativity for every possible node
cConservCheckAll :: CmdlState -> IO CmdlState
cConservCheckAll state = case i_state $ intState state of
    Nothing -> return $ genMsgAndCode "No library loaded" 1 state
    Just dgState -> do
      let lsNodes = getAllNodes dgState
      (resTxt, nle) <- conservativityList lsNodes
         (filter ((> None) . getNodeConservativity) lsNodes)
                                   (getAllEdges dgState)
                                   (i_libEnv dgState)
                                   (i_ln dgState)
      let nwst = state { intState = (intState state) {
                            i_state = Just dgState { i_libEnv = nle } } }
      return $ genMessage [] (flatConsRes resTxt) nwst

-- applies consistency check to the input
cConsistCheck :: CmdlState -> IO CmdlState
cConsistCheck = cDoLoop ConsCheck

-- applies consistency check to all possible input
cConsistCheckAll :: CmdlState -> IO CmdlState
cConsistCheckAll state = case i_state $ intState state of
      Nothing -> return $ genMsgAndCode "Nothing selected" 1 state
      Just pS -> case elements pS of
          [] -> return $ genMsgAndCode "Nothing selected" 1 state
          ls ->
             let ls' = map (\ (Element st nb) ->
                               Element (resetSelection st) nb) ls
                 nwSt = add2hist [ListChange [NodesChange $ elements pS]] $
                          state {
                           intState = (intState state) {
                              i_state = Just $ pS {
                                                  elements = ls' } } }
             in cConsistCheck nwSt

-- applies conservativity check to a given list
conservativityList :: [LNode DGNodeLab] -> [LNode DGNodeLab]
   -> [LEdge DGLinkLab] -> LibEnv -> LibName -> IO ([(String, String)], LibEnv)
conservativityList allNodes lsN lsE le libname = do
   (acc, libEnv') <- applyEdgeConservativity le libname lsE [] allNodes
   applyNodeConservativity libEnv' libname lsN acc

applyNodeConservativity :: LibEnv -> LibName -> [LNode DGNodeLab]
  -> [(String, String)] -> IO ([(String, String)], LibEnv)
applyNodeConservativity libEnv ln nds acc = case nds of
    [] -> return (acc, libEnv)
    n@(_, nlab) : ns -> do
      (str, nwLe, _) <- checkConservativityNode False n libEnv ln
      applyNodeConservativity nwLe ln ns
                         ((getDGNodeName nlab, str) : acc)

applyEdgeConservativity :: LibEnv -> LibName -> [LEdge DGLinkLab]
  -> [(String, String)] -> [LNode DGNodeLab] -> IO ([(String, String)], LibEnv)
applyEdgeConservativity le ln ls acc lsN = do
   let nameOf x lls = case find (\ (nb, _) -> nb == x) lls of
                      Nothing -> "Unknown node"
                      Just (_, nlab) -> getDGNodeName nlab
   case ls of
    [] -> return (acc, le)
    (x, y, edgLab) : l -> do
      (str, nwLe, _, _) <- checkConservativityEdge False (x, y, edgLab) le ln
      let nm = nameOf x lsN ++ arrowLink edgLab ++
               showEdgeId (dgl_id edgLab) ++ arrowLink edgLab
               ++ nameOf y lsN
      applyEdgeConservativity nwLe ln l ((nm, str) : acc) lsN
