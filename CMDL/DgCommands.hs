{- |
Module      :$Header$
Description : CMDL interface development graph commands
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

CMDL.DgCommands contains all development graph commands
that can be called from the CMDL interface
-}

module CMDL.DgCommands
       ( commandDgAll
       , commandDg
       , cUse
       , cDgThmHideShift
       , cDgSelect
       , cDgSelectAll
       , selectANode
       , wrapResultDg
       , wrapResultDgAll
       )where

import Interfaces.DataTypes
import Interfaces.Utils (emptyIntIState, getAllEdges, initNodeInfo)

import CMDL.DataTypes
    (CMDL_PrompterState(fileLoaded), CMDL_State(prompter, intState))
import CMDL.DataTypesUtils
    (getAllNodes, add2hist, genErrorMsg, genMessage, getIdComorphism)
import CMDL.Utils
    (decomposeIntoGoals, obtainEdgeList, obtainNodeList, prettyPrintErrList)

import Proofs.AbstractState (getProvers, initialState)
import Proofs.ComputeTheory (computeTheory)
import Proofs.TheoremHideShift (theoremHideShiftFromList)

import Static.GTheory (G_theory(G_theory), sublogicOfTh)
import Static.DevGraph (LibEnv, DGLinkLab, getDGNodeName)

import Driver.AnaLib (anaLib, anaLibExt)
import Driver.Options (hetcatsOpts)

import Common.LibName (LIB_NAME(getLIB_ID))
import Common.Utils (trim)
import Common.Result (Diagnosis(diagString), Result(Result))

import Comorphisms.KnownProvers (knownProversWithKind, shrinkKnownProvers)
import Comorphisms.LogicGraph (logicGraph)

import Logic.Comorphism (hasModelExpansion)
import Logic.Grothendieck (findComorphismPaths)
import Logic.Prover (ProverKind(ProveCMDLautomatic))

import Data.Graph.Inductive.Graph (LEdge)

import System.Environment

-- | Wraps Result structure around the result of a dg all style command
wrapResultDgAll :: (LIB_NAME->LibEnv -> LibEnv) ->
                   LIB_NAME -> LibEnv -> Result LibEnv
wrapResultDgAll fn lib_name lib_env
 = let res = fn lib_name lib_env
   in Result [] $ Just res


-- | Wraps Result structure around the result of a dg style command
wrapResultDg :: (LIB_NAME->[LEdge DGLinkLab] -> LibEnv -> LibEnv) ->
                LIB_NAME->[LEdge DGLinkLab] -> LibEnv -> Result LibEnv
wrapResultDg fn lib_name ls lib_env
 = let res = fn lib_name ls lib_env
   in Result [] $ Just res


-- | General function for implementing dg all style commands
commandDgAll :: ( LIB_NAME->LibEnv->Result LibEnv) -> CMDL_State
                      -> IO CMDL_State
commandDgAll fn state
 = case  i_state $ intState state of
    Nothing ->
                      -- just an error message and leave
                      -- the internal state intact so that
                      -- the interface can recover
               return $ genErrorMsg "No library loaded" state
    Just ist ->
        case fn (i_ln ist) (i_libEnv ist) of
         Result _ (Just nwLibEnv) ->
         -- Name of function is not known here, so an empty text is
         -- added as name, in a later stage (Shell.hs) the name will
         -- be inserted
           return $ add2hist [IStateChange $ Just ist] $ state {
              intState = (intState state) {
                           i_state=Just$ emptyIntIState nwLibEnv $ i_ln ist}
              }
         Result diag Nothing -> return $ genErrorMsg
                                     (concatMap diagString diag) state


-- | Generic function for a dg command, all other dg
-- commands are derived from this command by simply
-- specifing the function
commandDg ::  (LIB_NAME -> [LEdge DGLinkLab]->LibEnv->
              Result LibEnv) -> String -> CMDL_State
                      -> IO CMDL_State
commandDg fn input state
 = case i_state $ intState state of
    Nothing ->        -- leave the internal state intact so
                      -- that the interface can recover
                return $ genErrorMsg "No library loaded" state
    Just ist -> do
     let (_,edg,nbEdg,errs) = decomposeIntoGoals input
         tmpErrs =  prettyPrintErrList errs
     case (edg,nbEdg) of
       ([],[]) ->          -- leave the internal state intact so
                           -- that the interface can recover
                 return $ genErrorMsg (tmpErrs++"No edges in input string\n")
                              state
       (_,_) ->
        do
        let lsNodes   = getAllNodes ist
            lsEdges   = getAllEdges ist
            -- compute the list of edges from the input
            (errs',listEdges) = obtainEdgeList edg nbEdg lsNodes
                              lsEdges
            tmpErrs'  = tmpErrs ++ prettyPrintErrList errs'
        case listEdges of
         [] -> return $ genErrorMsg (tmpErrs' ++ "No edge in input string\n")
                              state
         _  ->
            case fn (i_ln ist) listEdges (i_libEnv ist) of
             Result _ (Just nwLibEnv) ->
               -- name added later !!
                 return $ add2hist [IStateChange $ Just ist]
                        $ genMessage tmpErrs' []
                      state {
                        intState = (intState state){
                          i_state=Just$ emptyIntIState nwLibEnv $ i_ln ist}
                        }
             Result diag Nothing -> return $ genErrorMsg
                        (concatMap diagString diag) state


-- | The function 'cUse' implements the Use commands, i.e.
-- given a path it tries to load the library  at that path
cUse::String ->CMDL_State -> IO CMDL_State
cUse input state
 = do
   -- options should be passed through from the top-level
   opts <- getArgs >>= hetcatsOpts
   let file = trim input
   tmp <- case i_state $ intState state of
           Nothing -> anaLib opts file
           Just dgState ->
                   anaLibExt opts file $ i_libEnv dgState
   case tmp of
    Nothing ->             -- leave internal state intact so that
                           -- the interface can recover
               return$ genErrorMsg ("Unable to load library "++input) state
    Just (nwLn, nwLibEnv) ->
                 return
                   state {
                     intState = IntState {
                          i_hist = IntHistory { undoList = [],
                                                redoList = []
                                              },
                          i_state = Just $   emptyIntIState nwLibEnv nwLn,
                          filename = file
                          },
                     prompter = (prompter state) {
                                          fileLoaded = file }
                     }

-- The only command that requires a list of nodes instead
-- of edges.
cDgThmHideShift :: String -> CMDL_State -> IO CMDL_State
cDgThmHideShift input state
 = case i_state $ intState state of
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
              tmpErrs' = tmpErrs ++ prettyPrintErrList errs'
          case listNodes of
           [] -> return $ genErrorMsg (tmpErrs'++"No nodes in input string\n")
                                 state
           _ ->
            do
             let
              Result diag nwLibEnv = theoremHideShiftFromList (i_ln dgState)
                                     listNodes (i_libEnv dgState)
              -- diag not used, how should it?
             case nwLibEnv of
              Nothing -> return $ genErrorMsg (concatMap diagString diag)
                                  state
               -- ADD TO HISTORY ??
              Just newEnv ->
                 return $ add2hist [IStateChange $ Just dgState] $
                     genMessage tmpErrs' []
                    state {
                       intState =
                        (intState state) {
                         i_state =Just $ emptyIntIState newEnv $ i_ln dgState
                         }
                           }

-- selection commands
selectANode :: Int -> IntIState
               -> [Int_NodeInfo]
selectANode x dgState
 = let
    -- computes the theory of a given node
    -- (i.e. solves DGRef cases and so on,
    -- see CASL Reference Manual, p.294, Def 4.9)
    gth = computeTheory (i_libEnv dgState) (i_ln dgState)
    nodeName t = case lookup t $ getAllNodes dgState of
                Nothing -> "Unknown node"
                Just ll -> getDGNodeName ll
   in
    case knownProversWithKind ProveCMDLautomatic of
     Result _ Nothing -> []
     Result _ (Just kpMap) ->
    -- if compute theory was successful give the
    -- result as one element list, otherwise an
    -- empty list
      case gth x of
       Result _ (Just th@(G_theory lid _ _ _ _)) ->
       -- le not used and should be
        do
         let sl = sublogicOfTh th
         tmp<-initialState
                lid
                (shows (getLIB_ID $ i_ln dgState) "_" ++ nodeName x)
                th
                (shrinkKnownProvers sl kpMap)
                (getProvers ProveCMDLautomatic sl $
                 filter hasModelExpansion $
                 findComorphismPaths logicGraph $
                 sublogicOfTh th
                )
         -- all goals and axioms are selected initialy in the proof status
         return (initNodeInfo tmp x)
       _ -> []

-- | function swithces interface in proving mode and also
-- selects a list of nodes to be used inside this mode
cDgSelect :: String -> CMDL_State -> IO CMDL_State
cDgSelect input state
 =case i_state $ intState state of
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
              tmpErrs' = tmpErrs ++ prettyPrintErrList errs'
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
                nwist = emptyIntIState (i_libEnv dgState) (i_ln dgState)
             return $ add2hist [IStateChange $ Just dgState] $
                   genMessage tmpErrs' []
                 state {
                   -- add the prove state to the status
                   -- containing all information selected
                   -- in the input
                   intState = (intState state) {
                               i_state = Just nwist {
                                          elements = elems,
                                          cComorphism = getIdComorphism elems
                                          } }
                   }


-- | Function switches the interface in proving mode by
-- selecting all nodes
cDgSelectAll :: CMDL_State -> IO CMDL_State
cDgSelectAll state
 =case i_state $ intState state of
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
          nwist = emptyIntIState (i_libEnv dgState) (i_ln dgState)
               -- ADD TO HISTORY
      return $ add2hist [IStateChange $ Just dgState] $ state {
              -- add the prove state to the status containing
              -- all information selected in the input
              intState = (intState state) {
                           i_state = Just nwist {
                                          elements = elems,
                                          cComorphism = getIdComorphism elems
                                            } }
              }
