{- |
Module      :$Header$
Description : CMDL interface development graph commands
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

PGIP.DgCommands contains all development graph commands
that can be called from the CMDL interface
-}

module PGIP.DgCommands
       ( commandDgAll
       , commandDg
       , cUse
       , cDgThmHideShift
       , cDgSelect
       , cDgSelectAll
       , selectANode
       )where

import PGIP.Utils
import PGIP.DataTypes
import PGIP.DataTypesUtils

import Proofs.AbstractState
import Proofs.TheoremHideShift

import Static.GTheory
import Static.DGToSpec
import Static.DevGraph
import Static.AnalysisLibrary

import Common.Result

import Data.Graph.Inductive.Graph
import Data.List

import Syntax.AS_Library

import Driver.Options

import Comorphisms.KnownProvers
import Comorphisms.LogicGraph

import Logic.Comorphism
import Logic.Grothendieck
import Logic.Prover


-- | General function for implementing dg all style commands
commandDgAll :: ( LIB_NAME->LibEnv->LibEnv) -> CMDL_State
                      -> IO CMDL_State
commandDgAll fn state
 = case devGraphState state of
    Nothing ->
                      -- just an error message and leave
                      -- the internal state intact so that
                      -- the interface can recover
               return $ genErrorMsg "No library loaded" state
    Just dgState ->
     do
      let nwLibEnv = fn (ln dgState) (libEnv dgState)
      return state {
              devGraphState = Just dgState { libEnv = nwLibEnv  },
              -- delete any selection if a dg command is used
              proveState = Nothing,
              prompter = (cleanPrompter $ prompter state )++"> "
              }


-- | Generic function for a dg command, all other dg
-- commands are derived from this command by simply
-- specifing the function
commandDg ::  (LIB_NAME -> [LEdge DGLinkLab]->LibEnv->
              LibEnv) -> String -> CMDL_State
                      -> IO CMDL_State
commandDg fn input state
 = case devGraphState state of
    Nothing ->        -- leave the internal state intact so
                      -- that the interface can recover
                return $ genErrorMsg "No library loaded" state
    Just dgState -> do
     let (_,edg,nbEdg,errs) = decomposeIntoGoals input
         tmpErrs =  prettyPrintErrList errs
     case (edg,nbEdg) of
       ([],[]) ->          -- leave the internal state intact so
                           -- that the interface can recover
                 return $genErrorMsg (tmpErrs++"No edges in input string\n")
                              state
       (_,_) ->
        do
        let lsNodes   = getAllNodes dgState
            lsEdges   = getAllEdges dgState
            -- compute the list of edges from the input
            (errs',listEdges) = obtainEdgeList edg nbEdg lsNodes
                              lsEdges
            tmpErrs'  = tmpErrs ++ (prettyPrintErrList errs')
        case listEdges of
         [] -> return $genErrorMsg (tmpErrs' ++ "No edge in input string\n")
                              state
         _  ->
           do
            let
              nwLibEnv = fn (ln dgState) listEdges
                            (libEnv dgState)
            return $ genMessage tmpErrs' []
                      state {
                        devGraphState = Just
                                  dgState { libEnv = nwLibEnv },
                        -- delete any selection if a dg command is
                        -- used
                        proveState = Nothing,
                        prompter = (cleanPrompter $ prompter state)++"> "
                        }


-- | The function 'cUse' implements the Use commands, i.e.
-- given a path it tries to load the library  at that path
cUse::String ->CMDL_State -> IO CMDL_State
cUse input state
 = do
   let opts = defaultHetcatsOpts
       file = trim input
   tmp <- case devGraphState state of
           Nothing -> anaLib opts file
           Just dgState ->
                   anaLibExt opts file $ libEnv dgState
   case tmp of
    Nothing ->             -- leave internal state intact so that
                           -- the interface can recover
               return$ genErrorMsg ("Unable to load library "++input) state
    Just (nwLn, nwLibEnv) ->
                 return
                   state {
                     devGraphState = Just
                                   CMDL_DevGraphState {
                                     ln = nwLn,
                                     libEnv = nwLibEnv },
                     prompter = (file ++ "> "),
                     -- delete any selection if a dg command is
                     -- used
                     proveState = Nothing,
                     history = CMDL_History {
                                 oldEnv = Just nwLibEnv,
                                 undoList = [],
                                 redoList = [],
                                 undoInstances = [],
                                 redoInstances = []
                                 }
                     }

-- The only command that requires a list of nodes instead
-- of edges.
cDgThmHideShift :: String -> CMDL_State -> IO CMDL_State
cDgThmHideShift input state
 = case devGraphState state of
    Nothing ->                -- leave internal state intact so
                              -- that the interface can recover
               return $ genErrorMsg "No library loaded" state
    Just dgState -> do
      let (nds,_,_,errs) = decomposeIntoGoals input
          tmpErrs = prettyPrintErrList errs
      case nds of
       [] ->               -- leave internal state intact so
                           -- that the interface can recover
             return $ genErrorMsg (tmpErrs++"No nodes in input string\n")
                          state
       _ ->
         do
          let lsNodes = getAllNodes dgState
              (errs',listNodes) = obtainNodeList nds lsNodes
              tmpErrs' = tmpErrs ++ (prettyPrintErrList errs')
          case listNodes of
           [] -> return $ genErrorMsg (tmpErrs'++"No nodes in input string\n")
                                 state
           _ ->
            do
             let
              Result diag nwLibEnv = theoremHideShiftFromList (ln dgState)
                                     listNodes (libEnv dgState)
              -- diag not used, how should it?
             case nwLibEnv of
              Nothing -> return $ genErrorMsg (concat $ map diagString diag)
                                  state
              Just newEnv -> return $ genMessage tmpErrs' []
                        state {
                          devGraphState = Just
                                          dgState { libEnv = newEnv },
                          proveState = Nothing,
                          prompter = (cleanPrompter $ prompter state)++"> "
                           }

-- selection commands
selectANode :: Int -> CMDL_DevGraphState
               -> [CMDL_ProofAbstractState]
selectANode x dgState
 = let
    -- computes the theory of a given node
    -- (i.e. solves DGRef cases and so on,
    -- see CASL Reference Manual, p.294, Def 4.9)
    -- computeTheory is defined in Static.DGToSpec
    gth n = computeTheory (libEnv dgState)
                          (ln dgState)
                          n
    nodeName t=case find(\(n,_)-> n==t) $ getAllNodes dgState of
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
       Result _ (Just (le, th@(G_theory lid _ _ _ _))) ->
       -- le not used and should be
        do
         let sl = sublogicOfTh th
         tmp<-initialState
                lid
                (shows
                   (getLIB_ID $ ln dgState) "_" ++(nodeName x)
                )
                th
                (shrinkKnownProvers sl kpMap)
                (getProvers ProveCMDLautomatic sl $
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
cDgSelect :: String -> CMDL_State -> IO CMDL_State
cDgSelect input state
 =case devGraphState state of
   Nothing ->              -- leave internal state intact so
                           -- that the interface can recover
              return $ genErrorMsg "No library loaded" state
   Just dgState -> do
    let (nds,_,_,errs) = decomposeIntoGoals input
        tmpErrs        = prettyPrintErrList errs
    case nds of
     [] -> return $ genErrorMsg (tmpErrs++"No nodes in input string\n") state
     _ ->
      case knownProversWithKind ProveCMDLautomatic of
       Result _ Nothing ->
           return $ genErrorMsg (tmpErrs++"No prover found\n") state
       Result _ (Just _) ->
        do
              -- list of all nodes
          let lsNodes = getAllNodes dgState
              -- list of input nodes
              (errs',listNodes) = obtainNodeList nds lsNodes
              tmpErrs' = tmpErrs ++ (prettyPrintErrList errs')
          case listNodes of
            [] -> return $ genErrorMsg(tmpErrs'++"No nodes in input string\n")
                              state
            _ ->
             do
             let
                -- elems is the list of all results (i.e.
                -- concat of all one element lists)
                elems = concatMap
                       (\x -> case x of
                               (n,_) -> selectANode n dgState
                               ) listNodes
                oldH = history state
                nwPrompter = case nds of
                              hd:[] -> (cleanPrompter $ prompter state)++"."++
                                         hd++"> "
                              hd:_ -> (cleanPrompter $ prompter state)++"."++
                                         hd++"^> "
                              _ -> prompter state
             return $ genMessage tmpErrs' []
                 state {
                   -- add the prove state to the status
                   -- containing all information selected
                   -- in the input
                   proveState = Just
                       CMDL_ProveState {
                         elements = elems,
                         cComorphism = Nothing,
                         prover = Nothing,
                         consChecker = Nothing,
                         save2file = False,
                         useTheorems = False,
                         script = [],
                         loadScript = False
                         },
                   history = oldH {
                        undoInstances = ([],[]):(undoInstances oldH),
                        redoInstances = []},
                   prompter = nwPrompter
                   }



-- | Function switches the interface in proving mode by
-- selecting all nodes
cDgSelectAll :: CMDL_State -> IO CMDL_State
cDgSelectAll state
 =case devGraphState state of
   Nothing -> return $ genErrorMsg "No library loaded" state
   Just dgState ->
    case knownProversWithKind ProveCMDLautomatic of
     Result _ Nothing -> return $ genErrorMsg "No prover found" state
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
          oldH = history state
          nwPrompter = case lsNodes of
                        hd:[] -> (cleanPrompter $ prompter state) ++
                                  "."++(getDGNodeName $ snd hd)++"> "
                        hd:_ -> (cleanPrompter $ prompter state) ++
                                  "."++(getDGNodeName $ snd hd)++"^> "
                        _ -> prompter state
      return state {
              -- add the prove state to the status containing
              -- all information selected in the input
              proveState = Just
                            CMDL_ProveState {
                              elements = elems,
                              cComorphism = Nothing,
                              prover = Nothing,
                              consChecker = Nothing,
                              save2file = False,
                              useTheorems = False,
                              script = [],
                              loadScript = False
                             },
              history = oldH {
                         undoInstances= ([],[]):(undoInstances oldH),
                         redoInstances= []
                         },
              prompter = nwPrompter
              }


