{- |
Module      :  $Header$
Description :  Gtk GUI for the prover
Copyright   :  (c) Thiemo Wiedemeyer, Uni Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  raider@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

This module provides a GUI for the prover.
-}

module GUI.GtkProverGUI
  (showProverGUI)
  where

import Graphics.UI.Gtk
import Graphics.UI.Gtk.Glade
--import Graphics.UI.Gtk.ModelView as MV

import GUI.GtkUtils
import qualified GUI.Glade.ProverGUI as ProverGUI

import Common.AS_Annotation as AS_Anno
import qualified Common.Doc as Pretty
import Common.Result as Result
import qualified Common.OrderedMap as OMap
import Common.ExtSign

import Control.Concurrent

import Proofs.AbstractState

import Logic.Comorphism
import Logic.Logic
import Logic.Prover

import qualified Comorphisms.KnownProvers as KnownProvers

import Static.GTheory

import Monad (when)

import Data.IORef
import qualified Data.Map as Map
import Data.List

-- | Displays the consistency checker window
showProverGUI ::
  (Logic lid sublogics1 basic_spec1 sentence symb_items1 symb_map_items1
         sign1 morphism1 symbol1 raw_symbol1 proof_tree1)
  => lid
  -> ProofActions lid sentence -- ^ record of possible GUI actions
  -> String -- ^ theory name
  -> String -- ^ warning information
  -> G_theory -- ^ theory
  -> KnownProvers.KnownProversMap -- ^ map of known provers
  -> [(G_prover,AnyComorphism)] -- ^ list of suitable comorphisms to provers
                                -- for sublogic of G_theory
  -> IO (Result.Result G_theory)
showProverGUI lid prGuiAcs thName warningTxt th knownProvers comorphList =
  postGUISync $ do
    xml                   <- getGladeXML ProverGUI.get
    -- get objects
    window                <- xmlGetWidget xml castToWindow "ProverGUI"
    -- buttons at buttom
    btnShowTheory         <- xmlGetWidget xml castToButton "btnShowTheory"
    btnShowSelectedTheory <- xmlGetWidget xml castToButton "btnShowSelectedTheory"
    btnClose              <- xmlGetWidget xml castToButton "btnClose"
    -- goals view
    trvGoals              <- xmlGetWidget xml castToTreeView "trvGoals"
    btnGoalsAll           <- xmlGetWidget xml castToButton "btnGoalsAll"
    btnGoalsNone          <- xmlGetWidget xml castToButton "btnGoalsNone"
    btnGoalsInvert        <- xmlGetWidget xml castToButton "btnGoalsInvert"
    btnGoalsSelectOpen    <- xmlGetWidget xml castToButton "btnGoalsSelectOpen"
    -- axioms view
    trvAxioms             <- xmlGetWidget xml castToTreeView "trvAxioms"
    btnAxiomsAll          <- xmlGetWidget xml castToButton "btnAxiomsAll"
    btnAxiomsNone         <- xmlGetWidget xml castToButton "btnAxiomsNone"
    btnAxiomsInvert       <- xmlGetWidget xml castToButton "btnAxiomsInvert"
    btnAxiomsFormer       <- xmlGetWidget xml castToButton "btnAxiomsFormer"
    -- theorems view
    trvTheorems           <- xmlGetWidget xml castToTreeView "trvTheorems"
    btnTheoremsAll        <- xmlGetWidget xml castToButton "btnTheoremsAll"
    btnTheoremsNone       <- xmlGetWidget xml castToButton "btnTheoremsNone"
    btnTheoremsInvert     <- xmlGetWidget xml castToButton "btnTheoremsInvert"
    -- status
    btnDisplay            <- xmlGetWidget xml castToButton "btnDisplay"
    btnProofDetails       <- xmlGetWidget xml castToButton "btnProofDetails"
    btnProve              <- xmlGetWidget xml castToButton "btnProve"
    lblStatus             <- xmlGetWidget xml castToLabel "lblStatus"
    lblSublogic           <- xmlGetWidget xml castToLabel "lblSublogic"
    -- prover
    trvProvers            <- xmlGetWidget xml castToTreeView "trvProvers"
    btnFineSelection      <- xmlGetWidget xml castToButton "btnFineSelection"

    set window [windowTitle := thName ++ " - Select Goal(s) and Prove"]

    initState <- (initialState lid thName th knownProvers comorphList
                  >>= recalculateSublogicF prGuiAcs)
    state <- newMVar initState
    axioms <- axiomMap initState

    putStrLn $ show $ Map.keys $ proversMap initState
    putStrLn $ show $ OMap.keys $ goalMap initState
    putStrLn $ show $ map (\ (k,s) -> if wasTheorem s then "(Th) " ++ k else k)
                    $ OMap.toList axioms
    putStrLn $ show $ OMap.keys $ goalMap initState
    -- set list data
    listProvers <- setListData trvProvers id $ Map.keys $ proversMap initState
    listGoals <- setListData trvGoals id $ OMap.keys $ goalMap initState
    listAxioms <- setListData trvAxioms id
                    $ map (\ (k,s) -> if wasTheorem s then "(Th) " ++ k else k)
                    $ OMap.toList axioms
    listTheorems <- setListData trvTheorems (id) $ OMap.keys $ goalMap initState

    -- setup provers list
    setListSelectorSingle trvProvers $ modifyMVar_ state
                                     $ selectProver trvProvers listProvers
    setSelectedProver trvProvers initState

    let action = modifyMVar_ state $ updateStatusSublogic lblSublogic trvGoals
                   listGoals trvAxioms listAxioms trvTheorems listTheorems
                   trvProvers listProvers prGuiAcs knownProvers

    -- setup goal list
    selectedGoals <- setListSelectorMultiple trvGoals btnGoalsAll btnGoalsNone
                       btnGoalsInvert action
    onClicked btnGoalsSelectOpen $ return ()

    -- setup axioms list
    selectedAxioms <- setListSelectorMultiple trvAxioms btnAxiomsAll
                        btnAxiomsNone btnAxiomsInvert action
    onClicked btnAxiomsFormer $ return ()

    -- setup theorems list
    selectedTheorems <- setListSelectorMultiple trvTheorems btnTheoremsAll
                          btnTheoremsNone btnTheoremsInvert action

    -- button bindings
    onClicked btnClose $ widgetDestroy window

    onClicked btnShowTheory $
      displayTheoryWithWarning "Theory" thName warningTxt th

    onClicked btnShowSelectedTheory $ do
      s <- readMVar state
      displayTheoryWithWarning "Selected Theory" thName warningTxt
                               (selectedTheory s)

    onClicked btnDisplay $ do
      s <- readMVar state
      s' <- updateStateGetSelectedGoals trvGoals listGoals s
      displayGoals s'
      return ()

    onClicked btnProofDetails $ return ()

    onClicked btnProve $ return ()

    onClicked btnFineSelection $ do
      s <- takeMVar state
      let s' = s { proverRunning = True }
      --updateDisplay s' True lb pathsLb statusLabel
      --disableWids wids
      --prState <- updateStatusSublogic s'
      Result.Result ds ms'' <- fineGrainedSelectionF prGuiAcs s'
      s'' <- case ms'' of
        Nothing -> do
          errorDialog "Error" (showRelDiags 2 ds)
          return s'
        Just res -> return res
      let s''' = s'' { proverRunning = False
                     , accDiags = accDiags s'' ++ ds }
      --enableWids wids
      --updateDisplay s''' True lb pathsLb statusLabel
      --putWinOnTop main
      putMVar state s'''

    widgetShow window
    return $ Result.Result { diags = []
                           , maybeResult = Nothing }

-- | Called whenever the button "Display" is clicked.
displayGoals ::
  (Logic lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
         sign1 morphism1 symbol1 raw_symbol1 proof_tree1)
  => ProofState lid1 sentence1
  -> IO ()
displayGoals s = case theory s of
  G_theory lid1 (ExtSign sig1 _) _ _ _ -> do
    let thName = theoryName s
        goalsText s' = show $ Pretty.vsep $
                       map (print_named lid1 .
                            AS_Anno.mapNamed (simplify_sen lid1 sig1)) $
                       toNamedList s'
        sens = selectedGoalMap s
    sens' <- coerceThSens (logicId s) lid1 "" sens
    textView ("Selected Goals from Theory " ++ thName) (goalsText sens')
             $ Just (thName ++ "-goals.txt")

setSelectedProver ::
  (Logic lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
         sign1 morphism1 symbol1 raw_symbol1 proof_tree1)
  => TreeView
  -> ProofState lid1 sentence1
  -> IO ()
setSelectedProver view s = do
  selector <- treeViewGetSelection view
  let ind = case selectedProver s of
              Just sp -> findIndex (==sp) $ Map.keys (proversMap s)
              Nothing -> Nothing
  maybe (return ()) (\i -> treeSelectionSelectPath selector [i]) ind

updateStatusSublogic ::
  (Logic lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
         sign1 morphism1 symbol1 raw_symbol1 proof_tree1)
  => Label -- ^ sublogic label
  -> TreeView -- ^ goals list
  -> ListStore String -- ^ goals list
  -> TreeView -- ^ axioms list
  -> ListStore String -- ^ axioms list store
  -> TreeView -- ^ theorems list
  -> ListStore String -- ^ theorems list store
  -> TreeView -- ^ provers list
  -> ListStore String -- ^ provers list store
  -> ProofActions lid1 sentence1 -- ^ record of possible GUI actions
  -> KnownProvers.KnownProversMap -- ^ map of known provers
  -> ProofState lid1 sentence1
  -> IO (ProofState lid1 sentence1)
updateStatusSublogic lbl gls listGls axs listAxs ths listThs prs listPrs
  prGuiAcs knownProvers s' = do
  s'' <- updateStateGetSelectedSens axs listAxs ths listThs s'
  s''' <- updateStateGetSelectedGoals gls listGls s''
  s <- recalculateSublogicF prGuiAcs $ (s''' {proversMap = knownProvers})
  labelSetText lbl $ show $ sublogicOfTheory s
  when (Map.keys (proversMap s') /= Map.keys (proversMap s))
       (do updateListData listPrs $ Map.keys $ proversMap s'
           setSelectedProver prs s)
  return s{ selectedProver =
              maybe Nothing (\ sp -> find (==sp) $ Map.keys (proversMap s))
                    (selectedProver s) }

updateStateGetSelectedGoals ::
  (Logic lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
         sign1 morphism1 symbol1 raw_symbol1 proof_tree1)
  => TreeView
  -> ListStore String
  -> ProofState lid1 sentence1
  -> IO (ProofState lid1 sentence1)
updateStateGetSelectedGoals view listGoals s = do
  selector <- treeViewGetSelection view
  rows <- treeSelectionGetSelectedRows selector
  goals <- mapM (\ (row:[]) -> listStoreGetValue listGoals row) rows
  return s { selectedGoals = goals }

updateStateGetSelectedSens ::
  (Logic lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
         sign1 morphism1 symbol1 raw_symbol1 proof_tree1)
  => TreeView -- ^ axioms listbox
  -> ListStore String
  -> TreeView -- ^ theorems listbox
  -> ListStore String
  -> ProofState lid1 sentence1
  -> IO (ProofState lid1 sentence1)
updateStateGetSelectedSens axs listAxs ths listThs s = do
  selectorAxs <- treeViewGetSelection axs
  selectorThs <- treeViewGetSelection ths
  rowsAxs <- treeSelectionGetSelectedRows selectorAxs
  rowsThs <- treeSelectionGetSelectedRows selectorThs
  axioms <- mapM (\ (row:[]) -> listStoreGetValue listAxs row) rowsAxs
  theorems <- mapM (\ (row:[]) -> listStoreGetValue listThs row) rowsThs
  return s { includedAxioms   = axioms
           , includedTheorems = theorems }

-- | Called whenever a prover is selected from the "Pick Theorem Prover" list.
selectProver ::
  (Logic lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
         sign1 morphism1 symbol1 raw_symbol1 proof_tree1)
  => TreeView
  -> ListStore String
  -> ProofState lid1 sentence1
  -> IO (ProofState lid1 sentence1)
selectProver view listPrs s = do
  selector <- treeViewGetSelection view
  ((row:[]):[]) <- treeSelectionGetSelectedRows selector
  prover <- listStoreGetValue listPrs row
  return s { selectedProver = Just prover }

