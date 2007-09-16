{- |
Module      :$Header$
Description : CMDL interface development graph commands
Copyright   : uni-bremen and DFKI
Licence     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
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
       , cDgSelect
       , cDgSelectAll
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

import Static.GTheory
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
commandDgAll :: String->( LIB_NAME->LibEnv->LibEnv) -> CMDLState
                      -> IO CMDLState
commandDgAll name fn state
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
      return $ register2history name state {
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
commandDg ::  String->(LIB_NAME -> [LEdge DGLinkLab]->LibEnv->
              LibEnv) -> String -> CMDLState
                      -> IO CMDLState
commandDg name fn input state
 = case devGraphState state of
    Nothing -> return state {
                      -- leave the internal state intact so
                      -- that the interface can recover
                      errorMsg = "No library loaded"
                      }
    Just dgState -> do
     let (_,edg,nbEdg,errs) = decomposeIntoGoals input
         tmpErrs =  prettyPrintErrList errs
     case (edg,nbEdg) of
       ([],[]) -> return
                    state {
                    -- leave the internal state intact so 
                    -- that the interface can recover
                    errorMsg = tmpErrs++"No edges in input string\n"
                    }
       (_,_) ->
        do
        let lsNodes   = getAllNodes dgState
            lsEdges   = getAllEdges dgState
            -- compute the list of edges from the input
            (errs',listEdges) = obtainEdgeList edg nbEdg lsNodes
                              lsEdges
            tmpErrs'  = tmpErrs ++ (prettyPrintErrList errs')
        case listEdges of
         [] -> return state {
                   errorMsg = tmpErrs' ++ "No edge in input string\n"
                      }
         _  -> 
           do
            let 
              nwLibEnv = fn (ln dgState) listEdges 
                            (libEnv dgState)
            return $register2history(name++" "++input)
                   state {
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
                      proveState = Nothing,
                      errorMsg = tmpErrs'
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
                 return$register2history ("use "++input) 
                   state {
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
                     proveState = Nothing,
                     oldEnv = Just nwLibEnv
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
          tmpErrs = prettyPrintErrList errs
      case nds of
       [] -> return
                    state {
                     -- leave internal state intact so 
                     -- that the interface can recover
                     errorMsg = tmpErrs++"No nodes in input string\n" 
                     }
       _ ->
         do
          let lsNodes = getAllNodes dgState
              (errs',listNodes) = obtainNodeList nds lsNodes
              tmpErrs' = tmpErrs ++ (prettyPrintErrList errs')
          case listNodes of
           [] -> return state {
                    errorMsg = tmpErrs' ++ "No nodes in input string\n"
                    }
           _ ->
            do 
             let
              nwLibEnv = theoremHideShiftFromList (ln dgState)
                            listNodes (libEnv dgState)
             return  $register2history ("do thm-hide "++input) state {
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
                   proveState = Nothing,
                   errorMsg = tmpErrs'
                   }


shellDgThmHideShift :: String -> Sh CMDLState ()
shellDgThmHideShift 
 = shellComWith cDgThmHideShift False False "dg thm-hide"

shellDgUse :: String -> Sh CMDLState ()
shellDgUse
 = shellComWith cUse False False "use"

shellDgAuto :: String -> Sh CMDLState ()
shellDgAuto 
 = shellComWith (commandDg "dg auto" automaticFromList) 
                        False False "dg auto"

shellDgGlobSubsume:: String -> Sh CMDLState ()
shellDgGlobSubsume 
 = shellComWith (commandDg "dg glob-subsume" globSubsumeFromList)
                False False "dg glob-subsume"

shellDgGlobDecomp:: String -> Sh CMDLState ()
shellDgGlobDecomp 
 = shellComWith (commandDg "dg glob-decomp" globDecompFromList) 
                False False "dg glob-decomp" 

shellDgLocInfer :: String -> Sh CMDLState ()
shellDgLocInfer 
 = shellComWith (commandDg  "dg loc-infer" localInferenceFromList) 
                False False "dg loc-infer"

shellDgLocDecomp :: String -> Sh CMDLState ()
shellDgLocDecomp 
 = shellComWith (commandDg  "dg loc-decomp" locDecompFromList) 
                False False "dg loc-decomp"

shellDgComp :: String -> Sh CMDLState () 
shellDgComp 
 = shellComWith (commandDg "dg comp" compositionFromList) 
               False False "dg comp"

shellDgCompNew :: String-> Sh CMDLState ()
shellDgCompNew
 = shellComWith (commandDg "dg comp-new" 
       compositionCreatingEdgesFromList) False False "dg comp-new"
shellDgHideThm :: String-> Sh CMDLState ()
shellDgHideThm 
 = shellComWith (commandDg "dg hide-thm"
       automaticHideTheoremShiftFromList) False False "dg hide-thm"
shellDgAllAuto::  Sh CMDLState ()
shellDgAllAuto 
 = shellComWithout (commandDgAll "dg-all auto" automatic) 
                     False False "dg-all auto"
                         
shellDgAllGlobSubsume :: Sh CMDLState ()
shellDgAllGlobSubsume 
 = shellComWithout (commandDgAll "dg-all glob-subsume" globSubsume) 
                   False False "dg-all glob-subsume"

shellDgAllGlobDecomp :: Sh CMDLState ()
shellDgAllGlobDecomp 
 = shellComWithout (commandDgAll "dg-all glob-decomp" globDecomp)
                   False False "dg-all glob-decomp"

shellDgAllLocInfer :: Sh CMDLState ()
shellDgAllLocInfer 
 = shellComWithout (commandDgAll "dg-all loc-infer" localInference) 
                   False False "dg-all loc-infer"

shellDgAllLocDecomp :: Sh CMDLState ()
shellDgAllLocDecomp 
 = shellComWithout (commandDgAll "dg-all loc-decomp" locDecomp)
                   False False "dg-all loc-decomp"

shellDgAllComp :: Sh CMDLState ()
shellDgAllComp 
 = shellComWithout (commandDgAll "dg-all comp" composition) 
                   False False "dg-all comp"

shellDgAllCompNew :: Sh CMDLState ()
shellDgAllCompNew 
 = shellComWithout (commandDgAll "dg-all comp-new" 
       compositionCreatingEdges) False False "dg-all comp-new"

shellDgAllHideThm :: Sh CMDLState ()
shellDgAllHideThm 
 = shellComWithout (commandDgAll "dg-all hide-thm" 
       automaticHideTheoremShift) False False "dg-all hide-thm"

shellDgAllThmHide :: Sh CMDLState ()
shellDgAllThmHide 
 = shellComWithout (commandDgAll "dg-all thm-hide"
                    theoremHideShift) False False "dg-all thm-hide"


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
        tmpErrs        = prettyPrintErrList errs
    case nds of
     [] -> return 
             state {
                 -- leave internal state intact so 
                 -- that the interface can recover
                    errorMsg = tmpErrs++"No nodes in input string\n"
                    }
     _ ->
      case knownProversWithKind ProveCMDLautomatic of
       Result _ Nothing -> return 
                             state {
                             -- leave internal state intact
                             -- so that the interface can
                             -- recover
                              errorMsg=tmpErrs++"No prover found\n"
                              }
       Result _ (Just _) ->         
        do
              -- list of all nodes
          let lsNodes = getAllNodes dgState
              -- list of input nodes
              (errs',listNodes) = obtainNodeList nds lsNodes
              tmpErrs' = tmpErrs ++ (prettyPrintErrList errs')
          case listNodes of
            [] -> return state {
                     errorMsg = tmpErrs'++ "No nodes in input string\n"
                     }
            _ -> 
             do
             let
                -- elems is the list of all results (i.e. 
                -- concat of all one element lists)
                elems = concatMap 
                       (\x -> case x of
                               (n,_) -> selectANode n dgState 
                               ) listNodes
             return $register2history ("select "++input) state {
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
                                   loadScript = False,
                                   historyList = ([],[])
                                   },
                   errorMsg = tmpErrs'
                   }



shellDgSelect :: String -> Sh CMDLState ()
shellDgSelect  
 = shellComWith cDgSelect False False "select"



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
      return $register2history "select-all" state {
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
                              loadScript = False,
                              historyList = ([],[])
                              }
              }


shellDgSelectAll :: Sh CMDLState ()
shellDgSelectAll
 = shellComWithout cDgSelectAll False False "select-all"

