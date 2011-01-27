{- |
Module      :$Header$
Description : CMDL interface development graph commands
Copyright   : uni-bremen and DFKI
License     : GPLv2 or higher, see LICENSE.txt
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
       , cExpand
       , cAddView
       , selectANode
       , wrapResultDg
       , wrapResultDgAll
       ) where

import Interfaces.DataTypes
import Interfaces.Utils (emptyIntIState, getAllEdges, initNodeInfo)

import CMDL.DataTypes

import CMDL.DataTypesUtils
    (getAllNodes, add2hist, genErrorMsg, genMessage, getIdComorphism,
     getInputDGNodes)
import CMDL.Utils (decomposeIntoGoals, obtainEdgeList, prettyPrintErrList)

import Proofs.AbstractState (comorphismsToProvers, getAllProvers, initialState)
import Proofs.TheoremHideShift (theoremHideShiftFromList)

import Static.AnalysisLibrary
import Static.GTheory (sublogicOfTh)
import Static.DevGraph
import Static.ComputeTheory (computeTheory)

import Driver.AnaLib (anaLib, anaLibExt)
import Driver.Options

import Comorphisms.KnownProvers (knownProversWithKind, shrinkKnownProvers)
import Comorphisms.LogicGraph (logicGraph)

import Logic.Prover (ProverKind (ProveCMDLautomatic))

import Syntax.AS_Structured
import Syntax.AS_Library

import Common.LibName (LibName (getLibId))
import Common.Utils (trim)
import Common.Result
import Common.ResultT
import Common.Id
import Common.AS_Annotation


import Data.Graph.Inductive.Graph (LEdge)
import qualified Data.Map as Map
import qualified Data.Set as Set

-- | Wraps Result structure around the result of a dg all style command
wrapResultDgAll :: (LibName -> LibEnv -> LibEnv)
                -> LibName -> LibEnv -> Result LibEnv
wrapResultDgAll fn lib_name = return . fn lib_name

-- | Wraps Result structure around the result of a dg style command
wrapResultDg :: (LibName -> [LEdge DGLinkLab] -> LibEnv -> LibEnv)
             -> LibName -> [LEdge DGLinkLab] -> LibEnv -> Result LibEnv
wrapResultDg fn lib_name ls = return . fn lib_name ls

-- | General function for implementing dg all style commands
commandDgAll :: (LibName -> LibEnv -> Result LibEnv)
             -> CmdlState -> IO CmdlState
commandDgAll fn state = case i_state $ intState state of
  Nothing -> return $ genErrorMsg "No library loaded" state
  Just ist -> case fn (i_ln ist) (i_libEnv ist) of
    Result _ (Just nwLibEnv) ->
         {- Name of function is not known here, so an empty text is
         added as name, in a later stage (Shell.hs) the name will
         be inserted -}
        return $ add2hist [IStateChange $ Just ist] $ state
             { intState = (intState state)
                 { i_state = Just $ emptyIntIState nwLibEnv $ i_ln ist } }
    Result diag Nothing ->
        return $ genErrorMsg (concatMap diagString diag) state

{- | Generic function for a dg command, all other dg
commands are derived from this command by simply
specifing the function -}
commandDg :: (LibName -> [LEdge DGLinkLab] -> LibEnv -> Result LibEnv)
          -> String -> CmdlState -> IO CmdlState
commandDg fn input state = case i_state $ intState state of
    Nothing -> return $ genErrorMsg "No library loaded" state
    Just ist -> do
     let (_, edg, nbEdg, errs) = decomposeIntoGoals input
         tmpErrs = prettyPrintErrList errs
     case (edg, nbEdg) of
       ([], []) ->
         -- leave the internal state intact so that the interface can recover
         return $ genErrorMsg (tmpErrs ++ "No edges in input string\n") state
       (_, _) -> do
        let lsNodes = getAllNodes ist
            lsEdges = getAllEdges ist
            -- compute the list of edges from the input
            (errs', listEdges) = obtainEdgeList edg nbEdg lsNodes lsEdges
            tmpErrs' = tmpErrs ++ prettyPrintErrList errs'
        case listEdges of
         [] -> return $ genErrorMsg (tmpErrs' ++ "No edge in input string\n")
                              state
         _ -> case fn (i_ln ist) listEdges (i_libEnv ist) of
             Result _ (Just nwLibEnv) ->
               -- name added later !!
                 return $ add2hist [IStateChange $ Just ist]
                   $ genMessage tmpErrs' [] state
                     { intState = (intState state)
                         { i_state = Just $ emptyIntIState nwLibEnv
                             $ i_ln ist } }
             Result diag Nothing ->
               return $ genErrorMsg (concatMap diagString diag) state

{- | The function 'cUse' implements the Use commands, i.e.
given a path it tries to load the library  at that path -}
cUse :: String -> CmdlState -> IO CmdlState
cUse input state = do
   let file = trim input
       opts = hetsOpts state
   tmp <- case i_state $ intState state of
           Nothing -> anaLib opts file
           Just dgState -> let
             le = i_libEnv dgState
             ln = i_ln dgState
             dg = lookupDGraph ln le
             initDG = cpIndexMaps dg emptyDG
             in anaLibExt opts file le initDG
   case tmp of
    Nothing ->
      -- leave the internal state intact so that the interface can recover
      return $ genErrorMsg ("Unable to load library " ++ input) state
    Just (nwLn, nwLibEnv) -> return state
      { intState = IntState
          { i_hist = IntHistory
              { undoList = []
              , redoList = [] }
          , i_state = Just $ emptyIntIState nwLibEnv nwLn
          , filename = file }
      , prompter = (prompter state)
          { fileLoaded = file } }

{- The only command that requires a list of nodes instead
of edges. -}
cDgThmHideShift :: String -> CmdlState -> IO CmdlState
cDgThmHideShift input state = case i_state $ intState state of
    Nothing -> return $ genErrorMsg "No library loaded" state
    Just dgState ->
      let (errors, nodes) = getInputDGNodes input dgState
       in if null nodes
            then return $ genErrorMsg errors state
            else let Result diag nwLibEnv = theoremHideShiftFromList
                        (i_ln dgState) nodes (i_libEnv dgState)
                     -- diag not used, how should it?
                  in return (case nwLibEnv of
                       Nothing -> genErrorMsg (concatMap diagString diag) state
                       -- ADD TO HISTORY ??
                       Just newEnv -> add2hist [IStateChange $ Just dgState] $
                                        genMessage errors [] state
                                          { intState = (intState state)
                                              { i_state = Just $ emptyIntIState
                                                                   newEnv $ i_ln
                                                                     dgState
                                               }
                                          })

-- selection commands
selectANode :: Int -> IntIState -> [Int_NodeInfo]
selectANode x dgState = let
    {- computes the theory of a given node
    (i.e. solves DGRef cases and so on,
    see CASL Reference Manual, p.294, Def 4.9) -}
    gth = computeTheory (i_libEnv dgState) (i_ln dgState)
    nodeName t = case lookup t $ getAllNodes dgState of
                Nothing -> "Unknown node"
                Just ll -> getDGNodeName ll
    in case knownProversWithKind ProveCMDLautomatic of
     Result _ Nothing -> []
     Result _ (Just kpMap) ->
    {- if compute theory was successful give the
    result as one element list, otherwise an
    empty list -}
      case gth x of
       Just th ->
       -- le not used and should be
         let sl = sublogicOfTh th
             tmp = (initialState
                (shows (getLibId $ i_ln dgState) "_" ++ nodeName x)
                th
                (shrinkKnownProvers sl kpMap))
                { comorphismsToProvers =
                    getAllProvers ProveCMDLautomatic sl logicGraph }
         -- all goals and axioms are selected initialy in the proof status
         in [initNodeInfo tmp x]
       _ -> []

{- | function swithces interface in proving mode and also
selects a list of nodes to be used inside this mode -}
cDgSelect :: String -> CmdlState -> IO CmdlState
cDgSelect input state = let iState = intState state in
  return $ case i_state iState of
    Nothing -> genErrorMsg "No library loaded" state
    Just dgState -> let (errors, nodes) = getInputDGNodes input dgState
      in if null nodes then genErrorMsg errors state else
      case maybeResult $ knownProversWithKind ProveCMDLautomatic of
        Nothing -> genErrorMsg (errors ++ "\nNo prover found") state
        Just _ -> let {- elems is the list of all results (i.e.
                      concat of all one element lists) -}
            elems = concatMap (flip selectANode dgState . fst) nodes
            nwist = emptyIntIState (i_libEnv dgState) (i_ln dgState)
         in add2hist [IStateChange $ Just dgState] $ genMessage errors [] state
           {- add the prove state to the status
           containing all information selected
           in the input -}
           { intState = iState
               { i_state = Just nwist
                   { elements = elems
                   , cComorphism = getIdComorphism elems } } }

cExpand :: String -> CmdlState -> IO CmdlState
cExpand input state = let iState = intState state in case i_state iState of
  Nothing -> return $ genErrorMsg "No library loaded to expand" state
  Just ist -> do
    let opts = hetsOpts state
        fname = trim input
        lg = logicGraph
        ln = i_ln ist
        libenv = i_libEnv ist
        dg = lookupDGraph ln libenv
    Result ds mres <- runResultT
      $ anaSourceFile lg opts Set.empty libenv dg fname
    return $ case mres of
      Nothing -> genErrorMsg
        ("Analysis failed:\n" ++ showRelDiags (verbose opts) ds) state
      Just (lN', libEnv') ->
       -- assume lN' is empty, ignored or identical to ln
        let dg' = lookupDGraph lN' libEnv'
            newLibEnv = Map.insert ln dg' $ Map.delete lN' libEnv'
        in state
          { intState = iState
              { i_state = Just $ emptyIntIState newLibEnv ln } }

cAddView :: String -> CmdlState -> IO CmdlState
cAddView input state = let iState = intState state in case i_state iState of
  Nothing -> return $ genErrorMsg "No library loaded to add view to" state
  Just ist -> do
    let libenv = i_libEnv ist
        ln = i_ln ist
        lg = logicGraph
        opts = hetsOpts state
        dg = lookupDGraph ln libenv
        [vn, spec1, spec2] = words input
        mkSpecInst s = Spec_inst (mkSimpleId s) [] nullRange
    Result ds tmp <- runResultT $ liftR $ anaViewDefn lg ln libenv dg opts
      (mkSimpleId vn) (Genericity (Params []) (Imported []) nullRange)
      (View_type (emptyAnno $ mkSpecInst spec1)
       (emptyAnno $ mkSpecInst spec2) nullRange) [] nullRange
    return $ case tmp of
      Nothing -> genErrorMsg
          ("View analysis failed:\n" ++ showRelDiags (verbose opts) ds) state
      Just (_, nwDg, nwLibEnv) ->
        let newLibEnv' = Map.insert ln nwDg nwLibEnv
        in state
          { intState = iState
              { i_state = Just $ emptyIntIState newLibEnv' ln } }

{- | Function switches the interface in proving mode by
selecting all nodes -}
cDgSelectAll :: CmdlState -> IO CmdlState
cDgSelectAll state = let iState = intState state in
  return $ case i_state iState of
  Nothing -> genErrorMsg "No library loaded" state
  Just dgState ->
    case maybeResult $ knownProversWithKind ProveCMDLautomatic of
      Nothing -> genErrorMsg "No prover found" state
      Just _ -> let
          -- list of all nodes
          lsNodes = getAllNodes dgState
          {- elems is the list of all results (i.e. concat
          of all one element lists) -}
          elems = concatMap (flip selectANode dgState . fst) lsNodes
          nwist = emptyIntIState (i_libEnv dgState) (i_ln dgState)
               -- ADD TO HISTORY
        in add2hist [IStateChange $ Just dgState] $ state
              {- add the prove state to the status containing
              all information selected in the input -}
              { intState = iState
                  { i_state = Just nwist
                      { elements = elems
                      , cComorphism = getIdComorphism elems } } }
