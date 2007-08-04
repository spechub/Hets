{- |
Module      :$Header$
Description : CMDL interface development graph commands
Copyright   : uni-bremen and DFKI
Licence     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@iu-bremen.de
Stability   : provisional
Portability : portable

PGIP.DgCommands contains all development graph commands 
that can be called from the CMDL interface
-} 

module PGIP.DgCommands 
       ( shellDgThmHideShift
       , shellDgUse
       , shellDgAuto
       , shellDgGlobSubsume
       , shellDgGlobDecomp
       , shellDgLocInfer
       , shellDgLocDecomp
       , shellDgComp
       , shellDgCompNew
       , shellDgHideThm
       , shellDgAllAuto
       , shellDgAllGlobSubsume
       , shellDgAllGlobDecomp
       , shellDgAllLocInfer
       , shellDgAllLocDecomp
       , shellDgAllComp
       , shellDgAllCompNew
       , shellDgAllHideThm
       , shellDgAllThmHide
       , shellDgSelect
       , shellDgSelectAll
       , cUse
       , selectANode
       )where

import PGIP.CMDLState
import PGIP.CMDLUtils
import PGIP.CMDLShell

import Proofs.Automatic
import Proofs.Composition
import Proofs.AbstractState
import Proofs.Global
import Proofs.HideTheoremShift
import Proofs.Local
import Proofs.TheoremHideShift 

import Static.DGToSpec
import Static.DevGraph
import Static.AnalysisLibrary

import Common.Result

import Data.Graph.Inductive.Graph
import Data.List

import Syntax.AS_Library

import System.Console.Shell.ShellMonad

import Driver.Options

import Comorphisms.KnownProvers
import Comorphisms.LogicGraph

import Logic.Prover
import Logic.Grothendieck

-- | General function for implementing dg all style commands
commandDgAll :: ( LIB_NAME->LibEnv->LibEnv) -> CMDLState
                      -> IO CMDLState
commandDgAll fn state
 = case devGraphState state of
    Nothing -> return state {
                      -- just an error message and leave
                      -- the internal state intact so that
                      -- the interface can recover
                      errorMsg = "No library loaded"
                      }
    Just dgState ->
     do 
      let nwLibEnv = fn (ln dgState) (libEnv dgState)
      return state {
              devGraphState = Just dgState {
                                    libEnv = nwLibEnv,
                                    -- are nodes left alone!?
                                    allEdges = [],
                                    allEdgesUpToDate = False},
              -- delete any selection if a dg command is used
              proveState = Nothing
              }


-- | Generic function for a dg command, all other dg 
-- commands are derived from this command by simply
-- specifing the function 
commandDg :: (LIB_NAME -> [LEdge DGLinkLab]->LibEnv->
              LibEnv) -> String -> CMDLState
                      -> IO CMDLState
commandDg fn input state
 = case devGraphState state of
    Nothing -> return state {
                      -- leave the internal state intact so
                      -- that the interface can recover
                      errorMsg = "No library loaded"
                      }
    Just dgState -> do
     let (_,edg,nbEdg,errs) = decomposeIntoGoals input
     prettyPrintErrList errs
     case (edg,nbEdg) of
       ([],[]) -> return
                    state {
                    -- leave the internal state intact so 
                    -- that the interface can recover
                    errorMsg = "No edges in input string"
                    }
       (_,_) ->
        do
        let lsNodes   = getAllNodes dgState
            lsEdges   = getAllEdges dgState
            -- compute the list of edges from the input
            (errs',listEdges) = obtainEdgeList edg nbEdg lsNodes
                              lsEdges
            nwLibEnv = fn (ln dgState) listEdges 
                            (libEnv dgState)
        prettyPrintErrList errs'                    
        return state {
                  devGraphState = Just
                                  dgState {
                                    libEnv = nwLibEnv,
                                    -- are nodes left alone!?
                                    allNodes = lsNodes,
                                    allNodesUpToDate = True,
                                    allEdges = [],
                                    allEdgesUpToDate = False
                                    },
                  -- delete any selection if a dg command is
                  -- used
                  proveState = Nothing
                  }


-- | The function 'cUse' implements the Use commands, i.e. 
-- given a path it tries to load the library  at that path
cUse::String ->CMDLState -> IO CMDLState
cUse input state
 = do
   let opts = defaultHetcatsOpts
       file = input
   tmp <- case devGraphState state of 
           Nothing -> anaLib opts file
           Just dgState -> 
                   anaLibExt opts file $ libEnv dgState
   case tmp of 
    Nothing -> return state {
                 -- leave internal state intact so that 
                 -- the interface can recover
                 errorMsg = ("Unable to load library "++input)
                    }
    Just (nwLn, nwLibEnv) ->
                 return state {
                  devGraphState = Just  
                                   CMDLDevGraphState {
                                     ln = nwLn,
                                     libEnv = nwLibEnv,
                                     allNodes = [],
                                     allNodesUpToDate = False,
                                     allEdges = [],
                                     allEdgesUpToDate = False
                                     },
                  prompter = (file ++ "> "),
                  -- delete any selection if a dg command is 
                  -- used
                  proveState = Nothing
                  }

-- The only command that requires a list of nodes instead
-- of edges.
cDgThmHideShift :: String -> CMDLState -> IO CMDLState
cDgThmHideShift input state
 = case devGraphState state of
    Nothing -> return state {
                       -- leave internal state intact so 
                       -- that the interface can recover
                       errorMsg = "No library loaded"
                       }
    Just dgState -> do
      let (nds,_,_,errs) = decomposeIntoGoals input
      prettyPrintErrList errs
      case nds of
       [] -> return
                    state {
                     -- leave internal state intact so 
                     -- that the interface can recover
                     errorMsg = "No nodes in input string" 
                     }
       _ ->
         do
          let lsNodes = getAllNodes dgState
              (errs',listNodes) = obtainNodeList nds lsNodes
              nwLibEnv = theoremHideShiftFromList (ln dgState)
                            listNodes (libEnv dgState)
          prettyPrintErrList errs'                  
          return state {
                   devGraphState = Just
                                    dgState {
                                     libEnv = nwLibEnv,
                                     -- are nodes left alone!?
                                     allNodes = lsNodes,
                                     allNodesUpToDate = True,
                                     -- are edges left alone!?
                                     allEdges = [],
                                     allEdgesUpToDate = False
                                     },
                   -- delte any selection if a dg command is
                   -- used
                   proveState = Nothing
                   }


shellDgThmHideShift :: String -> Sh CMDLState ()
shellDgThmHideShift 
 = shellComWith cDgThmHideShift False False

shellDgUse :: String -> Sh CMDLState ()
shellDgUse
 = shellComWith cUse False False

shellDgAuto :: String -> Sh CMDLState ()
shellDgAuto 
 = shellComWith (commandDg automaticFromList) False False

shellDgGlobSubsume:: String -> Sh CMDLState ()
shellDgGlobSubsume 
 = shellComWith (commandDg globSubsumeFromList) False False 

shellDgGlobDecomp:: String -> Sh CMDLState ()
shellDgGlobDecomp 
 = shellComWith (commandDg globDecompFromList) False False 

shellDgLocInfer :: String -> Sh CMDLState ()
shellDgLocInfer 
 = shellComWith (commandDg localInferenceFromList) False False

shellDgLocDecomp :: String -> Sh CMDLState ()
shellDgLocDecomp 
 = shellComWith (commandDg locDecompFromList) False False

shellDgComp :: String -> Sh CMDLState () 
shellDgComp 
 = shellComWith (commandDg compositionFromList) False False 

shellDgCompNew :: String-> Sh CMDLState ()
shellDgCompNew
 = shellComWith (commandDg compositionCreatingEdgesFromList)
                                           False False

shellDgHideThm :: String-> Sh CMDLState ()
shellDgHideThm 
 = shellComWith (commandDg automaticHideTheoremShiftFromList)
                                         False False

shellDgAllAuto::  Sh CMDLState ()
shellDgAllAuto 
 = shellComWithout (commandDgAll automatic) False False
                         
shellDgAllGlobSubsume :: Sh CMDLState ()
shellDgAllGlobSubsume 
 = shellComWithout (commandDgAll globSubsume) False False

shellDgAllGlobDecomp :: Sh CMDLState ()
shellDgAllGlobDecomp 
 = shellComWithout (commandDgAll globDecomp) False False 

shellDgAllLocInfer :: Sh CMDLState ()
shellDgAllLocInfer 
 = shellComWithout (commandDgAll localInference) False False

shellDgAllLocDecomp :: Sh CMDLState ()
shellDgAllLocDecomp 
 = shellComWithout (commandDgAll locDecomp) False False

shellDgAllComp :: Sh CMDLState ()
shellDgAllComp 
 = shellComWithout (commandDgAll composition) False False

shellDgAllCompNew :: Sh CMDLState ()
shellDgAllCompNew 
 = shellComWithout (commandDgAll compositionCreatingEdges) False False

shellDgAllHideThm :: Sh CMDLState ()
shellDgAllHideThm 
 = shellComWithout (commandDgAll automaticHideTheoremShift) False False

shellDgAllThmHide :: Sh CMDLState ()
shellDgAllThmHide 
 = shellComWithout (commandDgAll theoremHideShift) False False


-- selection commands
selectANode :: Int -> CMDLDevGraphState
               -> [CMDLProofAbstractState]
selectANode x dgState
 = let
    -- computes the theory of a given node 
    -- (i.e. solves DGRef cases and so on,
    -- see CASL Reference Manual, p.294, Def 4.9)
    -- computeTheory is defined in Static.DGToSpec
    gth n = computeTheory (libEnv dgState)     
                          (ln dgState)
                          n
    nodeName t=case find(\(n,_)-> n==t)$getAllNodes dgState of
                Nothing -> "Unknown node"
                Just (_,ll)-> getDGNodeName ll
   in
    case knownProversWithKind ProveCMDLautomatic of 
     Result _ Nothing -> []
     Result _ (Just kpMap) ->
    -- if compute theory was successful give the
    -- result as one element list, otherwise an
    -- empty list
      case gth x of
       Result _ (Just th@(G_theory lid _ _ _ _)) ->
        do
         tmp<-initialState 
                lid 
                (shows
                   (getLIB_ID$ ln dgState) "_" ++(nodeName x)
                )
                th 
                (shrinkKnownProvers (sublogicOfTh th) kpMap)
                (getProvers ProveCMDLautomatic $
                 filter hasModelExpansion $
                 findComorphismPaths logicGraph $
                 sublogicOfTh th
                )        
         -- make so that nothing (no goals, no axioms) are 
         -- selected initialy in the goal proof status
         return (initCMDLProofAbstractState tmp{
                             selectedGoals =case selectedGoals tmp of
                                             [] -> []
                                             s:_-> [s] 
                                             } x)
       _ -> []



-- | function swithces interface in proving mode and also 
-- selects a list of nodes to be used inside this mode
cDgSelect :: String -> CMDLState -> IO CMDLState
cDgSelect input state 
 =case devGraphState state of
   Nothing -> return state {
                       -- leave internal state intact so
                       -- that the interface can recover
                       errorMsg = "No library loaded"
                       }
   Just dgState -> do
    let (nds,_,_,errs) = decomposeIntoGoals input
    prettyPrintErrList errs
    case nds of
     [] -> return 
             state {
                 -- leave internal state intact so 
                 -- that the interface can recover
                    errorMsg = "No nodes in input string"
                    }
     _ ->
      case knownProversWithKind ProveCMDLautomatic of
       Result _ Nothing -> return 
                             state {
                             -- leave internal state intact
                             -- so that the interface can
                             -- recover
                              errorMsg="No prover found"
                              }
       Result _ (Just _) ->         
        do
              -- list of all nodes
          let lsNodes = getAllNodes dgState
              -- list of input nodes
              (errs',listNodes) = obtainNodeList nds lsNodes
              -- elems is the list of all results (i.e. 
              -- concat of all one element lists)
              elems = concatMap 
                       (\x -> case x of
                               (n,_) -> selectANode n dgState 
                               ) listNodes
          prettyPrintErrList errs'                     
          return state {
                   -- keep the list of nodes as up to date
                   devGraphState = Just 
                                    dgState {
                                      allNodes = lsNodes,
                                      allNodesUpToDate = True
                                      },
                   -- add the prove state to the status
                   -- containing all information selected
                   -- in the input
                   proveState = Just
                                 CMDLProveState {
                                   elements = elems,
                                   cComorphism = Nothing,
                                   prover = Nothing,
                                   save2file = False,
                                   useTheorems = False,
                                   script = "",
                                   loadScript = False
                                   }
                   }



shellDgSelect :: String -> Sh CMDLState ()
shellDgSelect  
 = shellComWith cDgSelect False False



-- | Function switches the interface in proving mode by
-- selecting all nodes
cDgSelectAll :: CMDLState -> IO CMDLState
cDgSelectAll state
 =case devGraphState state of
   Nothing -> return state {
                       -- leave internal state intact so 
                       -- that the interface can recover
                       errorMsg = "No library loaded"
                       }
   Just dgState ->
    case knownProversWithKind ProveCMDLautomatic of
     Result _ Nothing -> return 
                          state {
                           -- leave internal state intact so
                           -- that the interface can recover
                           errorMsg="No prover found"
                           }
     Result _ (Just _) ->
      do
          -- list of all nodes
      let lsNodes = getAllNodes dgState
          -- elems is the list of all results (i.e. concat
          -- of all one element lists)
          elems = concatMap
                   (\x -> case x of 
                           (n,_) -> selectANode n dgState
                           ) lsNodes
      return state {
              -- keep the list of nodes as up to date
              devGraphState = Just
                               dgState {
                                 allNodes = lsNodes,
                                 allNodesUpToDate = True
                                 },
              -- add the prove state to the status containing
              -- all information selected in the input
              proveState = Just
                            CMDLProveState {
                              elements = elems,
                              cComorphism = Nothing,
                              prover = Nothing,
                              save2file = False,
                              useTheorems = False,
                              script = "",
                              loadScript = False
                              }
              }


shellDgSelectAll :: Sh CMDLState ()
shellDgSelectAll
 = shellComWithout cDgSelectAll False False

