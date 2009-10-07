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
import CMDL.Utils(decomposeIntoGoals, obtainEdgeList, prettyPrintErrList)

import Proofs.AbstractState (getProvers, initialState)
import Static.ComputeTheory (computeTheory)
import Proofs.TheoremHideShift (theoremHideShiftFromList)

import Static.GTheory (G_theory(G_theory), sublogicOfTh)
import Static.DevGraph (LibEnv, DGLinkLab, getDGNodeName)

import Driver.AnaLib (anaLib, anaLibExt)

import Common.LibName (LibName(getLibId))
import Common.Utils (trim)
import Common.Result (hasErrors, Diagnosis(diagString), Result(Result))

import Comorphisms.KnownProvers (knownProversWithKind, shrinkKnownProvers)
import Comorphisms.LogicGraph (logicGraph)

import Logic.Comorphism (hasModelExpansion)
import Logic.Grothendieck (currentLogic, findComorphismPaths)
import Logic.Prover (ProverKind(ProveCMDLautomatic))

import Data.Graph.Inductive.Graph (LEdge)

import Driver.Options
import Data.Maybe
import Data.List(isPrefixOf)
import Static.AnalysisLibrary
import Syntax.AS_Structured
import Syntax.AS_Library
import Driver.ReadFn
import Common.ResultT
import Common.Id
import Common.AS_Annotation
import Control.Monad
import System.Directory

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
         -- Name of function is not known here, so an empty text is
         -- added as name, in a later stage (Shell.hs) the name will
         -- be inserted
        return $ add2hist [IStateChange $ Just ist] $ state
             { intState = (intState state)
                 { i_state = Just $ emptyIntIState nwLibEnv $ i_ln ist } }
    Result diag Nothing ->
        return $ genErrorMsg (concatMap diagString diag) state

-- | Generic function for a dg command, all other dg
-- commands are derived from this command by simply
-- specifing the function
commandDg :: (LibName -> [LEdge DGLinkLab] -> LibEnv -> Result LibEnv)
          -> String -> CmdlState -> IO CmdlState
commandDg fn input state = case i_state $ intState state of
    Nothing -> return $ genErrorMsg "No library loaded" state
    Just ist -> do
     let (_, edg, nbEdg, errs) = decomposeIntoGoals input
         tmpErrs =  prettyPrintErrList errs
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
         _  -> case fn (i_ln ist) listEdges (i_libEnv ist) of
             Result _ (Just nwLibEnv) ->
               -- name added later !!
                 return $ add2hist [IStateChange $ Just ist]
                   $ genMessage tmpErrs' [] state
                     { intState = (intState state)
                         { i_state=Just$ emptyIntIState nwLibEnv $ i_ln ist } }
             Result diag Nothing ->
               return $ genErrorMsg (concatMap diagString diag) state

-- | The function 'cUse' implements the Use commands, i.e.
-- given a path it tries to load the library  at that path
cUse :: String -> CmdlState -> IO CmdlState
cUse input state = do
   let file = trim input
       opts = hetsOpts state
   tmp <- case i_state $ intState state of
           Nothing -> anaLib opts file
           Just dgState ->
                   anaLibExt opts file $ i_libEnv dgState
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

-- The only command that requires a list of nodes instead
-- of edges.
cDgThmHideShift :: String -> CmdlState -> IO CmdlState
cDgThmHideShift input state = case i_state $ intState state of
    Nothing      -> return $ genErrorMsg "No library loaded" state
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
    -- computes the theory of a given node
    -- (i.e. solves DGRef cases and so on,
    -- see CASL Reference Manual, p.294, Def 4.9)
    gth = computeTheory (i_libEnv dgState) (i_ln dgState)
    nodeName t = case lookup t $ getAllNodes dgState of
                Nothing -> "Unknown node"
                Just ll -> getDGNodeName ll
    in case knownProversWithKind ProveCMDLautomatic of
     Result _ Nothing -> []
     Result _ (Just kpMap) ->
    -- if compute theory was successful give the
    -- result as one element list, otherwise an
    -- empty list
      case gth x of
       Result _ (Just th@(G_theory lid _ _ _ _)) -> do
       -- le not used and should be
         let sl = sublogicOfTh th
         tmp <- initialState
                lid
                (shows (getLibId $ i_ln dgState) "_" ++ nodeName x)
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
cDgSelect :: String -> CmdlState -> IO CmdlState
cDgSelect input state = case i_state $ intState state of
   Nothing      -> return $ genErrorMsg "No library loaded" state
   Just dgState ->
     let (errors, nodes) = getInputDGNodes input dgState
      in if null nodes
           then return $ genErrorMsg errors state
           else case knownProversWithKind ProveCMDLautomatic of
                  Result _ Nothing ->
                    return $ genErrorMsg (errors ++ "\nNo prover found") state
                  Result _ (Just _) ->
                    let -- elems is the list of all results (i.e.
                        -- concat of all one element lists)
                        elems = concatMap (flip selectANode dgState . fst) nodes
                        nwist = emptyIntIState (i_libEnv dgState) (i_ln dgState)
                     in return $ add2hist [IStateChange $ Just dgState]
                           $ genMessage errors [] state
                               -- add the prove state to the status
                               -- containing all information selected
                               -- in the input
                               { intState = (intState state)
                                   { i_state = Just nwist
                                       { elements = elems
                                       , cComorphism = getIdComorphism elems }
                                    }
                               }

cExpand :: String -> CmdlState -> IO CmdlState
cExpand input state = do
   let opts = hetsOpts state
       fname = trim input
   fname' <- existsAnSource opts {intype = GuessIn} fname
   case fname' of
     Nothing -> return $ genErrorMsg "No source found" state
     Just file -> do
          curDir <- getCurrentDirectory
          input' <- readFile file
          mt <- getModificationTime file
          let absolutePath = if "/" `isPrefixOf` file
                             then file
                             else curDir ++ '/':file
              lg = logicGraph
              ln = i_ln istate
              istate = fromJust $ i_state $ intState state
              libenv = i_libEnv istate
              Result _ mast = readLibDefnM lg opts absolutePath input' mt
          case mast of
            Just (Lib_defn _ alibItems _ _) -> do
              let dg = fromJust $ Map.lookup ln libenv
              Result _ res <- runResultT $ foldM ana
                 ([], dg, libenv, lg) (map item alibItems)
              case res of
                Just (_, dg', libenv', _) ->
                    return state {
                       intState = (intState state) {
                          i_state = Just $ emptyIntIState (Map.insert ln dg' libenv') ln
                          }
                       }
                Nothing -> return $ genErrorMsg "Analysis failed" state
              where
              ana (libItems', dg1, libenv1, lG) libItem =
                let newLG = case libItems' of
                     [] -> lG { currentLogic = defLogic opts }
                     Logic_decl (Logic_name logTok _) _ : _ ->
                        lG { currentLogic = tokStr logTok }
                     _ -> lG
                in ResultT (do
                  Result diags2 res <-
                    runResultT $ anaLibItem newLG opts Set.empty libenv1 dg1 libItem
                  runResultT $ showDiags1 opts (liftR (Result diags2 res))
                  let mRes = case res of
                       Just (libItem', dg1', libenv1') ->
                            Just (libItem' : libItems', dg1', libenv1', newLG)
                       Nothing -> Nothing
                  if outputToStdout opts then
                     if hasErrors diags2 then
                        fail "Stopped due to errors"
                        else runResultT $ liftR $ Result [] mRes
                    else
                        runResultT $ liftR $ Result diags2 mRes)
            Nothing -> return $ genErrorMsg "Source can't be parsed" state

                                                   

cAddView :: String -> CmdlState -> IO CmdlState
cAddView input state = do
   let istate = fromJust $ i_state $ intState state
       libenv = i_libEnv istate
       ln = i_ln istate
       lg = logicGraph
       opts = hetsOpts state
       dg = fromJust $ Map.lookup ln libenv
       [vn,spec1,spec2] = words input
   Result _ tmp <- runResultT $ liftR $ anaViewDefn lg libenv dg opts Token{tokStr=vn,tokPos=nullRange}
                   (Genericity (Params []) (Imported[]) nullRange)
                   (View_type (Annoted {item=Spec_inst Token{tokStr=spec1,tokPos=nullRange}
                                        [] nullRange,opt_pos=nullRange,l_annos=[],r_annos=[]})
                    (Annoted {item=Spec_inst Token{tokStr=spec2,tokPos=nullRange} [] nullRange,opt_pos=nullRange,l_annos=[],r_annos=[]})
                    nullRange) [] nullRange
   case tmp of
    Nothing ->             -- leave internal state intact so that
                           -- the interface can recover
               return $ genErrorMsg ("Unable to add view "++vn) state
    Just (_, nwDg, nwLibEnv) ->
                 let nwLibEnv' = Map.insert ln nwDg nwLibEnv
                 in
                 return
                 state {
                     intState = (intState state) {
                          i_state = Just $ emptyIntIState nwLibEnv' ln
                          }
                     }

-- | Function switches the interface in proving mode by
-- selecting all nodes
cDgSelectAll :: CmdlState -> IO CmdlState
cDgSelectAll state = case i_state $ intState state of
   Nothing -> return $ genErrorMsg "No library loaded" state
   Just dgState ->
    case knownProversWithKind ProveCMDLautomatic of
     Result _ Nothing -> return $ genErrorMsg "No prover found" state
     Result _ (Just _) -> do
          -- list of all nodes
      let lsNodes = getAllNodes dgState
          -- elems is the list of all results (i.e. concat
          -- of all one element lists)
          elems = concatMap (flip selectANode dgState . fst) lsNodes
          nwist = emptyIntIState (i_libEnv dgState) (i_ln dgState)
               -- ADD TO HISTORY
      return $ add2hist [IStateChange $ Just dgState] $ state
              -- add the prove state to the status containing
              -- all information selected in the input
              { intState = (intState state)
                  { i_state = Just nwist
                      { elements = elems
                      , cComorphism = getIdComorphism elems } } }
