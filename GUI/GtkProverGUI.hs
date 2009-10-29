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

import GUI.GtkUtils
import qualified GUI.Glade.ProverGUI as ProverGUI

import Common.AS_Annotation as AS_Anno
import qualified Common.Doc as Pretty
import qualified Common.Result as Result
import qualified Common.OrderedMap as OMap
import Common.ExtSign

import Control.Concurrent.MVar

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

{- ProverGUI -}

-- | Displays the consistency checker window
showProverGUI ::
  (Logic lid sublogics basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree)
  => lid
  -> ProofActions lid sentence -- ^ record of possible GUI actions
  -> String -- ^ theory name
  -> String -- ^ warning information
  -> G_theory -- ^ theory
  -> KnownProvers.KnownProversMap -- ^ map of known provers
  -> [(G_prover,AnyComorphism)] -- ^ list of suitable comorphisms to provers
                                -- for sublogic of G_theory
  -> IO (Result.Result G_theory)
showProverGUI lid prGuiAcs thName warningTxt th knownProvers comorphList = do
  initState <- (initialState lid thName th knownProvers comorphList
                >>= recalculateSublogicF prGuiAcs)
  state <- newMVar initState
  wait <- newEmptyMVar
  postGUIAsync $ do
    xml                   <- getGladeXML ProverGUI.get
    -- get objects
    window                <- xmlGetWidget xml castToWindow "ProverGUI"
    -- buttons at buttom
    btnShowTheory         <- xmlGetWidget xml castToButton "btnShowTheory"
    btnShowSelectedTheory <- xmlGetWidget xml castToButton "btnShowSelected"
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
    lblComorphism         <- xmlGetWidget xml castToLabel "lblComorphism"
    lblSublogic           <- xmlGetWidget xml castToLabel "lblSublogic"
    -- prover
    trvProvers            <- xmlGetWidget xml castToTreeView "trvProvers"
    btnFineGrained        <- xmlGetWidget xml castToButton "btnFineGrained"

    windowSetTitle window $ "Prove: " ++ thName

    axioms <- axiomMap initState

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

    let update = updateStatusSublogic lblSublogic trvGoals listGoals trvAxioms
                   listAxioms trvTheorems listTheorems trvProvers listProvers
                   prGuiAcs knownProvers
        action = modifyMVar_ state $ update

    -- setup goal list
    selectedGoals' <- setListSelectorMultiple trvGoals btnGoalsAll btnGoalsNone
                        btnGoalsInvert action
    onClicked btnGoalsSelectOpen $ modifyMVar_ state $ (\ s -> do
      (Just model) <- treeViewGetModel trvGoals
      selector <- treeViewGetSelection trvGoals
      let
        isOpen st =
          let thst = thmStatus st
          in if null thst
            then True
            else case maximum $ map snd $ thst of
              BasicProof _ pst -> isOpenGoal $ goalStatus pst
              _ -> False
        select iter = do
          (row:[]) <- treeModelGetPath model iter
          key <- listStoreGetValue listGoals row
          if maybe (error "goal lookup") isOpen $ OMap.lookup key $ goalMap s
            then do
              modifyIORef selectedGoals' ((row:[]):)
              treeSelectionSelectIter selector iter
            else treeSelectionUnselectIter selector iter
          return False
      writeIORef selectedGoals' []
      treeModelForeach model select
      s' <- update s
      return s')

    -- setup axioms list
    selectedAxioms <- setListSelectorMultiple trvAxioms btnAxiomsAll
                        btnAxiomsNone btnAxiomsInvert action
    onClicked btnAxiomsFormer $ modifyMVar_ state $ (\ s -> do
      aM <- axiomMap s
      (Just model) <- treeViewGetModel trvAxioms
      selector <- treeViewGetSelection trvAxioms
      let
        isNotFormerTheorem st = not $ wasTheorem st
        select iter = do
          (row:[]) <- treeModelGetPath model iter
          key <- listStoreGetValue listAxioms row
          k <- case stripPrefix "(Th) " key of
            Just k -> return k
            Nothing -> return key
          if maybe (error "axiom lookup") isNotFormerTheorem $ OMap.lookup k aM
            then do
              modifyIORef selectedAxioms ((row:[]):)
              treeSelectionSelectIter selector iter
            else treeSelectionUnselectIter selector iter
          return False
      writeIORef selectedAxioms []
      treeModelForeach model select
      s' <- update s
      return s')

    -- setup theorems list
    setListSelectorMultiple trvTheorems btnTheoremsAll btnTheoremsNone
                            btnTheoremsInvert action

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
      displayGoals s

    onClicked btnProofDetails $ return ()

    onClicked btnProve $ return ()

    onClicked btnFineGrained $ forkIO_ $ modifyMVar_ state $ (\ s -> do
      let s' = s { proverRunning = True }
      prState <- update s'
      Result.Result ds ms'' <- fineGrainedSelectionF prGuiAcs prState
      s'' <- case ms'' of
        Nothing -> do
          -- Is error needed?
          --errorDialog "Error" (showRelDiags 2 ds)
          return s'
        Just res -> return res
      return s'' { proverRunning = False
                 , accDiags = accDiags s'' ++ ds })

    onDestroy window $ putMVar wait ()

    widgetShow window

  _ <- takeMVar wait
  return $ Result.Result { Result.diags = []
                         , Result.maybeResult = Nothing }

-- | Called whenever the button "Display" is clicked.
displayGoals ::
  (Logic lid sublogics basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree)
  => ProofState lid sentence
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
     TreeView
  -> ProofState lid sentence
  -> IO ()
setSelectedProver view s = do
  selector <- treeViewGetSelection view
  let ind = case selectedProver s of
              Just sp -> findIndex (==sp) $ Map.keys (proversMap s)
              Nothing -> Nothing
  maybe (return ()) (\i -> treeSelectionSelectPath selector [i]) ind

updateStatusSublogic ::
     Label -- ^ sublogic label
  -> TreeView -- ^ goals list
  -> ListStore String -- ^ goals list
  -> TreeView -- ^ axioms list
  -> ListStore String -- ^ axioms list store
  -> TreeView -- ^ theorems list
  -> ListStore String -- ^ theorems list store
  -> TreeView -- ^ provers list
  -> ListStore String -- ^ provers list store
  -> ProofActions lid sentence -- ^ record of possible GUI actions
  -> KnownProvers.KnownProversMap -- ^ map of known provers
  -> ProofState lid sentence
  -> IO (ProofState lid sentence)
updateStatusSublogic lbl gls listGls axs listAxs ths listThs prs listPrs
  prGuiAcs knownProvers s' = do
  s'' <- updateStateGetSelectedSens axs listAxs ths listThs s'
  s''' <- updateStateGetSelectedGoals gls listGls s''
  s <- recalculateSublogicF prGuiAcs $ (s''' {proversMap = knownProvers})
  setSublogic lbl $ show $ sublogicOfTheory s
  when (Map.keys (proversMap s') /= Map.keys (proversMap s))
       (do updateListData listPrs $ Map.keys $ proversMap s'
           setSelectedProver prs s)
  return s{ selectedProver =
              maybe Nothing (\ sp -> find (==sp) $ Map.keys (proversMap s))
                    (selectedProver s) }

updateStateGetSelectedGoals ::
     TreeView
  -> ListStore String
  -> ProofState lid sentence
  -> IO (ProofState lid sentence)
updateStateGetSelectedGoals view listGoals s = do
  selector <- treeViewGetSelection view
  rows <- treeSelectionGetSelectedRows selector
  goals <- mapM (\ (row:[]) -> listStoreGetValue listGoals row) rows
  return s { selectedGoals = goals }

updateStateGetSelectedSens ::
     TreeView -- ^ axioms listbox
  -> ListStore String
  -> TreeView -- ^ theorems listbox
  -> ListStore String
  -> ProofState lid sentence
  -> IO (ProofState lid sentence)
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
     TreeView
  -> ListStore String
  -> ProofState lid sentence
  -> IO (ProofState lid sentence)
selectProver view listPrs s = do
  selector <- treeViewGetSelection view
  ((row:[]):[]) <- treeSelectionGetSelectedRows selector
  prover <- listStoreGetValue listPrs row
  return s { selectedProver = Just prover }

-- | Called to set sublogic label
setSublogic :: Label -> String -> IO ()
setSublogic label text = labelSetLabel label $ "<b>" ++ text ++ "</b>"

