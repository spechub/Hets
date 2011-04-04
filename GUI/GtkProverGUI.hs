{- |
Module      :  $Header$
Description :  Gtk GUI for the prover
Copyright   :  (c) Thiemo Wiedemeyer, Uni Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  raider@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

This module provides a GUI for the prover.
-}

module GUI.GtkProverGUI ( showProverGUI ) where

import Graphics.UI.Gtk
import Graphics.UI.Gtk.Glade

import GUI.GtkUtils
import qualified GUI.Glade.ProverGUI as ProverGUI
import GUI.HTkProofDetails -- not implemented in Gtk

import Common.AS_Annotation as AS_Anno
import qualified Common.Doc as Pretty
import Common.Result
import qualified Common.OrderedMap as OMap
import Common.ExtSign
import Common.Utils

import Control.Concurrent.MVar

import Proofs.AbstractState

import Logic.Comorphism
import Logic.Logic
import Logic.Prover

import qualified Comorphisms.KnownProvers as KnownProvers

import Static.GTheory

import qualified Data.Map as Map
import Data.List
import Data.Maybe (fromMaybe, isJust )

data GProver = GProver
  { pName :: String
  , comorphism :: [AnyComorphism]
  , selected :: Int }

-- ProverGUI

-- | Displays the consistency checker window
showProverGUI :: ProofActions -- ^ record of possible GUI actions
  -> String -- ^ theory name
  -> String -- ^ warning information
  -> G_theory -- ^ theory
  -> KnownProvers.KnownProversMap -- ^ map of known provers
  -> [(G_prover, AnyComorphism)]
     -- ^ list of suitable comorphisms to provers for sublogic of G_theory
  -> IO (Result G_theory)
showProverGUI prGuiAcs thName warn th knownProvers comorphList = do
  initState <- recalculateSublogicF prGuiAcs
    (initialState thName th knownProvers)
    { comorphismsToProvers = comorphList }
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
    cbComorphism          <- xmlGetWidget xml castToComboBox "cbComorphism"
    lblSublogic           <- xmlGetWidget xml castToLabel "lblSublogic"
    -- prover
    trvProvers            <- xmlGetWidget xml castToTreeView "trvProvers"

    windowSetTitle window $ "Prove: " ++ thName

    -- set list data
    listProvers <- setListData trvProvers pName []
    listGoals <- setListData trvGoals showGoal $ toGoals initState
    listAxioms <- setListData trvAxioms id $ toAxioms initState
    listTheorems <- setListData trvTheorems id $ selectedGoals initState

    -- setup comorphism combobox
    comboBoxSetModelText cbComorphism
    shC <- after cbComorphism changed $ modifyMVar_ state
      $ setSelectedComorphism trvProvers listProvers cbComorphism

    -- setup provers list
    shP <- setListSelectorSingle trvProvers $ modifyMVar_ state
      $ setSelectedProver trvProvers listProvers cbComorphism shC

    -- setup axioms list
    shA <- setListSelectorMultiple trvAxioms btnAxiomsAll btnAxiomsNone
      btnAxiomsInvert $ modifyMVar_ state
      $ setSelectedAxioms trvAxioms listAxioms

    onClicked btnAxiomsFormer $ do
      signalBlock shA
      sel <- treeViewGetSelection trvAxioms
      treeSelectionSelectAll sel
      rs <- treeSelectionGetSelectedRows sel
      mapM_ ( \ ~p@(row : []) -> do
        i <- listStoreGetValue listAxioms row
        (if wasATheorem initState (stripPrefixAxiom i)
          then treeSelectionUnselectPath else treeSelectionSelectPath) sel p) rs
      signalUnblock shA
      modifyMVar_ state $ setSelectedAxioms trvAxioms listAxioms

   -- setup theorems list
    setListSelectorMultiple trvTheorems btnTheoremsAll btnTheoremsNone
      btnTheoremsInvert $ modifyMVar_ state
      $ setSelectedTheorems trvTheorems listTheorems

    let noProver = [ toWidget btnProve
                   , toWidget cbComorphism
                   , toWidget lblSublogic ]
        noAxiom = [ toWidget btnAxiomsAll
                  , toWidget btnAxiomsNone
                  , toWidget btnAxiomsInvert
                  , toWidget btnAxiomsFormer ]
        noTheory = [ toWidget btnTheoremsAll
                   , toWidget btnTheoremsNone
                   , toWidget btnTheoremsInvert ]
        noGoal = [ toWidget btnGoalsAll
                 , toWidget btnGoalsNone
                 , toWidget btnGoalsInvert
                 , toWidget btnGoalsSelectOpen ]
        prove = [toWidget window]
        update s' = do
          signalBlock shP
          s <- setSelectedProver trvProvers listProvers cbComorphism shC
            =<< updateProver trvProvers listProvers
            =<< updateSublogic lblSublogic prGuiAcs knownProvers
            =<< setSelectedGoals trvGoals listGoals s'
          signalUnblock shP
          activate noProver
            (isJust (selectedProver s) && not (null $ selectedGoals s))
          return s
    let hasGoals = not . null $ selectedGoals initState
    activate noGoal hasGoals
    activate noAxiom (not . null $ includedAxioms initState)
    activate noTheory hasGoals

    -- setup goal list
    shG <- setListSelectorMultiple trvGoals btnGoalsAll btnGoalsNone
      btnGoalsInvert $ modifyMVar_ state update

    onClicked btnGoalsSelectOpen $ do
      signalBlock shG
      sel <- treeViewGetSelection trvGoals
      treeSelectionSelectAll sel
      rs <- treeSelectionGetSelectedRows sel
      mapM_ ( \ ~p@(row : []) -> do
        g <- listStoreGetValue listGoals row
        (if gStatus g `elem` [GOpen, GTimeout]
          then treeSelectionSelectPath else treeSelectionUnselectPath) sel p) rs
      signalUnblock shG
      modifyMVar_ state update

    -- button bindings
    onClicked btnClose $ widgetDestroy window

    onClicked btnShowTheory $ displayTheoryWithWarning "Theory" thName warn th

    onClicked btnShowSelectedTheory $ readMVar state >>=
      displayTheoryWithWarning "Selected Theory" thName warn . selectedTheory

    onClicked btnDisplay $ readMVar state >>= displayGoals

    onClicked btnProofDetails $ forkIO_ $ readMVar state >>= doShowProofDetails

    onClicked btnProve $ do
      s' <- takeMVar state
      activate prove False
      forkIOWithPostProcessing (proveF prGuiAcs s')
        $ \ (Result ds ms) -> do
            s <- case ms of
              Nothing -> errorDialog "Error" (showRelDiags 2 ds) >> return s'
              Just res -> return res
            activate prove True
            signalBlock shG
            updateGoals trvGoals listGoals s
            signalUnblock shG
            putMVar state =<< update s { proverRunning = False
                                       , accDiags = accDiags s ++ ds }

    onDestroy window $ putMVar wait ()

    selectAllRows trvTheorems
    selectAllRows trvAxioms
    selectAllRows trvGoals

    widgetShow window

  _ <- takeMVar wait
  s <- takeMVar state
  return Result
    { diags = accDiags s
    , maybeResult = Just $ currentTheory s }

-- | Called whenever the button "Display" is clicked.
displayGoals :: ProofState -> IO ()
displayGoals s = case currentTheory s of
  G_theory lid1 (ExtSign sig1 _) _ sens1 _ -> do
    let thName = theoryName s
        goalsText = show . Pretty.vsep
          . map (print_named lid1 . AS_Anno.mapNamed (simplify_sen lid1 sig1))
          . toNamedList $ filterMapWithList (selectedGoals s) sens1
    textView ("Selected Goals from Theory " ++ thName) goalsText
             $ Just (thName ++ "-goals.txt")

updateComorphism :: TreeView -> ListStore GProver -> ComboBox
                 -> ConnectId ComboBox -> IO ()
updateComorphism view list cbComorphism sh = do
  signalBlock sh
  model <- comboBoxGetModelText cbComorphism
  listStoreClear model
  mfinder <- getSelectedSingle view list
  case mfinder of
    Just (_, f) -> do
      mapM_ (comboBoxAppendText cbComorphism) $ expand f
      comboBoxSetActive cbComorphism $ selected f
    Nothing -> return ()
  signalUnblock sh

expand :: GProver -> [String]
expand = map show . comorphism

setSelectedComorphism :: TreeView -> ListStore GProver -> ComboBox -> ProofState
  -> IO ProofState
setSelectedComorphism view list cbComorphism s = do
  mfinder <- getSelectedSingle view list
  case mfinder of
    Just (i, f) -> do
      sel <- comboBoxGetActive cbComorphism
      let nf = f { selected = sel }
      listStoreSetValue list i nf
      return $ setGProver nf s
    Nothing -> return s

setGProver :: GProver -> ProofState -> ProofState
setGProver f s =
  let pn = pName f
      c = comorphism f !! selected f
  in s
  { selectedProver = Just pn
  , proversMap = Map.insert pn [c] $ proversMap s}

updateSublogic :: Label -> ProofActions
               -> KnownProvers.KnownProversMap -> ProofState
               -> IO ProofState
updateSublogic lbl prGuiAcs knownProvers s' = do
  s <- recalculateSublogicF prGuiAcs s'
    { proversMap = Map.unionWith (++) (proversMap s') knownProvers }
  labelSetLabel lbl $ show $ sublogicOfTheory s
  return s

updateProver :: TreeView -> ListStore GProver -> ProofState
             -> IO ProofState
updateProver trvProvers listProvers s = do
  let new = toProvers s
  old <- listStoreToList listProvers
  let prvs = map (\ p -> case find ((pName p ==) . pName) old of
          Nothing -> p
          Just p' -> let oldC = comorphism p' !! selected p' in
            p { selected = fromMaybe 0 $ findIndex (== oldC) $ comorphism p }
        ) new
  updateListData listProvers prvs
  case selectedProver s of
    Just p -> case findIndex ((p ==) . pName) prvs of
      Just i -> do
        sel <- treeViewGetSelection trvProvers
        treeSelectionSelectPath sel [i]
      Nothing -> selectFirst trvProvers
    Nothing -> selectFirst trvProvers
  return s

updateGoals :: TreeView -> ListStore Goal -> ProofState -> IO ()
updateGoals trvGoals listGoals s = do
  let ng = toGoals s
  sel <- getSelectedMultiple trvGoals listGoals
  updateListData listGoals ng
  selector <- treeViewGetSelection trvGoals

  mapM_ (\ (_, Goal { gName = n }) -> treeSelectionSelectPath selector
      [fromMaybe (error "Goal not found!") $ findIndex ((n ==) . gName) ng]
    ) sel

setSelectedGoals :: TreeView -> ListStore Goal -> ProofState
                 -> IO ProofState
setSelectedGoals trvGoals listGoals s = do
  goals <- getSelectedMultiple trvGoals listGoals
  return s { selectedGoals = map (gName . snd) goals }

setSelectedAxioms :: TreeView -> ListStore String -> ProofState
                  -> IO ProofState
setSelectedAxioms axs listAxs s = do
  axioms <- getSelectedMultiple axs listAxs
  return s { includedAxioms = map (stripPrefixAxiom . snd) axioms }

setSelectedTheorems :: TreeView -> ListStore String -> ProofState
                    -> IO ProofState
setSelectedTheorems ths listThs s = do
  theorems <- getSelectedMultiple ths listThs
  return s { includedTheorems = map snd theorems }

stripPrefixAxiom :: String -> String
stripPrefixAxiom a = fromMaybe a $ stripPrefix "(Th) " a

-- | Called whenever a prover is selected from the "Pick Theorem Prover" list.
setSelectedProver :: TreeView -> ListStore GProver -> ComboBox
                  -> ConnectId ComboBox -> ProofState
                  -> IO ProofState
setSelectedProver trvProvers listProvers cbComorphism shC s = do
  mprover <- getSelectedSingle trvProvers listProvers
  updateComorphism trvProvers listProvers cbComorphism shC
  return $ case mprover of
    Nothing -> s { selectedProver = Nothing }
    Just (_, gp) -> setGProver gp s

wasATheorem :: ProofState -> String -> Bool
wasATheorem st i = case currentTheory st of
   G_theory _ _ _ sens _ -> maybe False wasTheorem $ OMap.lookup i sens

toGoals :: ProofState -> [Goal]
toGoals = sort . map toGtkGoal . getGoals

toProvers :: ProofState -> [GProver]
toProvers = Map.elems . foldr (\ (p', c) m ->
    let n = getProverName p'
        p = Map.findWithDefault (GProver n [] 0) n m in
    Map.insert n (p { comorphism = c : comorphism p}) m
  ) Map.empty . comorphismsToProvers
