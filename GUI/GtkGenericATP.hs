{- |
Module      :  ./GUI/GtkGenericATP.hs
Description :  Gtk Generic Prover GUI.
Copyright   :  (c) Thiemo Wiedemeyer, Uni Bremen 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  raider@informatik.uni-bremen.de
Stability   :  provisional
Portability :  needs POSIX

Generic Gtk GUI for automatic theorem provers.
-}

module GUI.GtkGenericATP ( genericATPgui ) where

import Graphics.UI.Gtk

import GUI.GtkUtils
import qualified GUI.Glade.GenericATP as GenericATP

import Interfaces.GenericATPState

import Control.Concurrent (forkIO, killThread, yield)
import Control.Concurrent.MVar
import Control.Monad (unless, when)
import qualified Control.Monad.Fail as Fail

import Common.AS_Annotation as AS_Anno
import Common.GtkGoal
import Common.Result
import Common.Utils (getEnvSave, readMaybe)

import Proofs.BatchProcessing

import Data.List
import Data.Maybe (fromMaybe, fromJust)
import qualified Data.Map as Map

import Logic.Prover

genericATPgui :: (Show sentence, Ord proof_tree, Ord sentence)
              => ATPFunctions sign sentence mor proof_tree pst
              -- ^ prover specific functions
              -> Bool -- ^ prover supports extra options
              -> String -- ^ prover name
              -> String -- ^ theory name
              -> Theory sign sentence proof_tree {- ^ theory consisting of a
                 signature and a list of Named sentence -}
              -> [FreeDefMorphism sentence mor] -- ^ freeness constraints
              -> proof_tree -- ^ initial empty proof_tree
              -> IO [ProofStatus proof_tree] -- ^ proof status for each goal
genericATPgui atpFun hasEOptions prName thName th freedefs pt = do
  result <- newEmptyMVar
  postGUIAsync $ do
    builder <- getGTKBuilder GenericATP.get
    -- get objects
    window <- builderGetObject builder castToWindow "GenericATP"
    -- buttons at buttom
    btnClose <- builderGetObject builder castToButton "btnClose"
    btnHelp <- builderGetObject builder castToButton "btnHelp"
    btnSaveConfig <- builderGetObject builder castToButton "btnSaveConfig"
    -- goal list
    trvGoals <- builderGetObject builder castToTreeView "trvGoals"
    -- options area
    sbTimeout <- builderGetObject builder castToSpinButton "sbTimeout"
    entryOptions <- builderGetObject builder castToEntry "entryOptions"
    cbIncludeProven <- builderGetObject builder castToCheckButton "cbIncludeProven"
    cbSaveBatch <- builderGetObject builder castToCheckButton "cbSaveBatch"
    -- prove buttons
    btnStop <- builderGetObject builder castToButton "btnStop"
    btnProveSelected <- builderGetObject builder castToButton "btnProveSelected"
    btnProveAll <- builderGetObject builder castToButton "btnProveAll"
    -- status and axioms
    lblStatus <- builderGetObject builder castToLabel "lblStatus"
    trvAxioms <- builderGetObject builder castToTreeView "trvAxioms"
    -- info and save buttons
    btnSaveProblem <- builderGetObject builder castToButton "btnSaveProblem"
    btnShowDetails <- builderGetObject builder castToButton "btnShowDetails"

    windowSetTitle window $ prName ++ ": " ++ thName

    let widgets = [toWidget entryOptions | hasEOptions] ++
                  [ toWidget btnClose , toWidget btnShowDetails
                  , toWidget btnHelp , toWidget btnSaveConfig
                  , toWidget sbTimeout
                  , toWidget cbIncludeProven , toWidget btnProveSelected
                  , toWidget btnProveSelected, toWidget btnProveAll
                  , toWidget lblStatus , toWidget btnSaveProblem ]
        switch = activate widgets
        switchAll b = do
          activate widgets b
          widgetSetSensitive btnStop $ not b

        -- setting up state
        initState = initialGenericState prName (initialProverState atpFun)
                      (atpTransSenName atpFun) th freedefs pt
        initGoals = goalsList initState

    stateMVar <- newMVar initState
    threadId <- newEmptyMVar
    finished <- newEmptyMVar

    -- setting up lists
    listGoals <- setListData trvGoals showGoal $ toGoals initState
    listAxioms <- setListData trvAxioms id []

    -- short update function
    let update' s = update s trvGoals listGoals listAxioms lblStatus sbTimeout
                           entryOptions
        save s = saveConfigCurrent s pt prName sbTimeout entryOptions

    -- set list selector and action
    setListSelectorSingle trvAxioms $ return ()
    setListSelectorSingle trvGoals $ do
      s'' <- takeMVar stateMVar
      -- saving options for previous selected goal
      s' <- save s''
      -- setting new selected goal
      mSelected <- getSelectedSingle trvGoals listGoals
      let s = maybe s' (\ (_, Goal { gName = n }) -> s' { currentGoal = Just n})
                    mSelected
      putMVar stateMVar s
      update' s

    -- setting options
    spinButtonSetValue sbTimeout $ fromIntegral guiDefaultTimeLimit
    widgetSetSensitive entryOptions hasEOptions
    widgetSetSensitive btnStop False
    enableSaveBatch <- getEnvSave False "HETS_ENABLE_BATCH_SAVE" readMaybe
    widgetSetSensitive cbSaveBatch enableSaveBatch

    -- setting save button name
    let ext = case problemOutput $ fileExtensions atpFun of
                e@('.' : _) -> e
                e -> '.' : e
    buttonSetLabel btnSaveProblem $ "Save " ++ tail ext ++ " File"

    -- bindings
    onClicked btnHelp $
      textView (prName ++ " Help") (proverHelpText atpFun) Nothing

    -- save config
    onClicked btnSaveConfig $ do
      state <- readMVar stateMVar
      -- save actual config
      s <- save state
      let cfgText = show $ printCfgText $ configsMap s
      textView (prName ++ " Configuration for Theory " ++ thName) cfgText
               $ Just $ thName ++ theoryConfiguration (fileExtensions atpFun)

    -- save problem output
    onClicked btnSaveProblem $ do
      state <- readMVar stateMVar
      -- save actual config
      s <- save state
      maybe (return ()) (\ g -> do
          inclProven <- toggleButtonGetActive cbIncludeProven
          let (nGoal, lp') = prepareLP (proverState s) s g inclProven
          prob <- goalOutput atpFun lp' nGoal $ createProverOptions atpFun
                    $ getConfig prName g pt $ configsMap s
          textView (prName ++ " Problem for Goal " ++ g) prob
            $ Just (thName ++ '_' : g ++ ext)
        ) $ currentGoal s

    -- show details of selected goal
    onClicked btnShowDetails $ do
      s <- readMVar stateMVar
      case currentGoal s of
        Nothing -> errorDialog "Error" "Please select a goal first."
        Just g -> do
          let res = Map.lookup g $ configsMap s
              output = maybe ["This goal hasn't been run through the prover."]
                             resultOutput res
              detailsText = concatMap ('\n' :) output
          textView (prName ++ " Output for Goal " ++ g)
            (seq (length detailsText) detailsText) $ Just $ g ++ ext

    -- show details of selected goal
    onClicked btnStop $ do
      tryTakeMVar threadId >>= maybe (error "MVar 'tId' not set") killThread
      putMVar finished ()

    -- show details of selected goal
    onClicked btnProveSelected $ do
      state <- takeMVar stateMVar
      -- save actual config
      s <- save state
      case currentGoal s of
        Nothing -> error "No goal selected."
        Just g -> do
          (_, exit) <- pulseBar "Proving" g
          inclProven <- toggleButtonGetActive cbIncludeProven
          let (nGoal, lp') = prepareLP (proverState s) s g inclProven
              cfg = configsMap s
          switch False
          forkIOWithPostProcessing
            (runProver atpFun lp' (getConfig prName g pt cfg) False thName nGoal)
            $ \ (retval, cfg') -> do
              case retval of
                ATPError m -> errorDialog "Error" m
                _ -> return ()
              let s' = s { configsMap = adjustOrSetConfig (\ c -> c
                           { timeLimitExceeded = isTimeLimitExceeded retval
                           , proofStatus = (proofStatus cfg')
                             { usedTime = timeUsed cfg' }
                           , resultOutput = resultOutput cfg'
                           , timeUsed = timeUsed cfg' }) prName g pt cfg }
              putMVar stateMVar s'
              updateGoals s' trvGoals listGoals
              exit
              switch True

    -- show details of selected goal
    onClicked btnProveAll $ do
      state <- readMVar stateMVar
      -- save actual config
      s <- save state
      let openGoalsMap = filterOpenGoals $ configsMap s
          numGoals = Map.size openGoalsMap
      if Map.null openGoalsMap then
        infoDialog "No open goals" "No open goals, nothing to do."
        else do
        timeout <- spinButtonGetValueAsInt sbTimeout
        opts' <- entryGetText entryOptions
        saveBatch <- toggleButtonGetActive cbSaveBatch
        inclProven <- toggleButtonGetActive cbIncludeProven
        (updat, exit) <- progressBar "Proving" "please wait..."
        let firstGoalName = head $ filter (`Map.member` openGoalsMap)
                              $ map AS_Anno.senAttr $ goalsList s
            opts = words opts'
            afterEachProofAttempt gPSF nSen nextSen cfg@(retval, _) = do
              cont <- goalProcessed stateMVar timeout opts numGoals prName
                                    gPSF nSen False cfg
              postGUISync $ do
                case retval of
                  ATPError m -> errorDialog "Error" m
                  _ -> return ()
                s' <- readMVar stateMVar
                updateGoals s' trvGoals listGoals
                let progress = fromIntegral gPSF / fromIntegral numGoals
                when cont $ updat progress $ AS_Anno.senAttr $ fromJust nextSen
                return cont
        updat 0 firstGoalName
        tid <- forkIO $ do
          yield
          genericProveBatch False timeout opts inclProven saveBatch
            afterEachProofAttempt (atpInsertSentence atpFun) (runProver atpFun)
            prName thName s Nothing
          b <- isEmptyMVar threadId
          unless b $ putMVar finished ()
        b <- tryPutMVar threadId tid
        unless b $ error "MVar 'threadId' already set"
        switchAll False
        forkIO_ $ do
          takeMVar finished
          tryTakeMVar threadId
          postGUIAsync $ do
            switchAll True
            exit

    onClicked btnClose $ widgetDestroy window

    -- read proofstate and store it in mvar
    onDestroy window $ do
      s <- takeMVar stateMVar
      let Result _ prst = revertRenamingOfLabels s $
            map ((\ g -> let res = Map.lookup g $ configsMap s
                             g' = Map.findWithDefault
                                    (error $ "Lookup of name failed: (1) " ++
                                           "should not happen \"" ++ g ++ "\"")
                                    g $ namesMap s
                  in maybe (openProofStatus g' prName $ currentProofTree s)
                           proofStatus res) . AS_Anno.senAttr) (goalsList s)
      putMVar result prst

    if null initGoals then do
        errorDialog "No goals available!" "No need to start prove window!"
        widgetDestroy window
      else do
        selectFirst trvGoals
        widgetShow window

  -- waiting for results
  res <- takeMVar result
  maybe (Fail.fail "reverse translation of names failed") return res

  where
    prepareLP prS s g' inclProven =
      let goals = goalsList s
          cfg = configsMap s
          idx = fromMaybe (error "Goal not found!")
                  $ findIndex ((== g') . AS_Anno.senAttr) goals
          (beforeThis, afterThis) = splitAt idx goals
          g = head afterThis -- Why use head and not goal?
          proved = filter (checkGoal cfg . AS_Anno.senAttr) beforeThis
      in if inclProven
        then (g, foldl (\ lp provedGoal -> atpInsertSentence atpFun lp
                            (provedGoal { AS_Anno.isAxiom = True }))
                          prS $ reverse proved)
        else (g, prS)

saveConfigCurrent :: (Ord proof_tree)
                  => GenericState sentence proof_tree pst -> proof_tree
                  -> String -> SpinButton -> Entry
                  -> IO (GenericState sentence proof_tree pst)
saveConfigCurrent s pt prName sbTimeout entryOptions = do
  -- saving options for previous selected goal
  timeout <- spinButtonGetValueAsInt sbTimeout
  opts <- entryGetText entryOptions
  let mn = currentGoal s
      cfg = maybe (configsMap s) (\ g ->
              adjustOrSetConfig (setExtraOpts $ words opts) prName g pt
                $ adjustOrSetConfig (setTimeLimit timeout) prName g pt
                $ configsMap s) mn
  return $ s { configsMap = cfg }

updateGoals :: GenericState sentence proof_tree pst -> TreeView
            -> ListStore Goal -> IO ()
updateGoals s trvGoals listGoals = do
  let ng = toGoals s
  selected <- getSelectedSingle trvGoals listGoals
  updateListData listGoals ng
  case selected of
    Just (_, Goal { gName = n }) -> do
      selector <- treeViewGetSelection trvGoals
      treeSelectionSelectPath selector
        [fromMaybe (error "Goal not found!") $ findIndex ((n ==) . gName) ng]
    Nothing -> return ()

-- | Updates the display of the status of the current goal.
update :: GenericState sentence proof_tree pst -> TreeView
       -> ListStore Goal -> ListStore String -> Label -> SpinButton -> Entry
       -> IO ()
update s trvGoals listGoals listAxioms lblStatus sbTimeout entryOptions = do
  -- update status and axioms
  selected <- getSelectedSingle trvGoals listGoals
  case selected of
    Just (_, Goal { gName = n, gStatus = stat }) -> do
      let cfg = Map.findWithDefault (error "GUI.GenericATP.updateDisplay") n
                  $ configsMap s
      spinButtonSetValue sbTimeout $ fromIntegral
        $ fromMaybe guiDefaultTimeLimit $ timeLimit cfg
      entrySetText entryOptions $ unwords $ extraOpts cfg
      labelSetLabel lblStatus $ show stat
      updateListData listAxioms $ usedAxioms $ proofStatus cfg
    Nothing -> return ()

-- | Utility function to set the time limit of a Config.
setTimeLimit :: Int -> GenericConfig proof_tree -> GenericConfig proof_tree
setTimeLimit n c = c { timeLimit = if n > 0 then Just n else Nothing }

-- | Utility function to set the extra options of a Config.
setExtraOpts :: [String] -> GenericConfig proof_tree -> GenericConfig proof_tree
setExtraOpts opts c = c { extraOpts = opts }

toGoals :: GenericState sentence proof_tree pst -> [Goal]
toGoals s = sort $ map (\ g ->
  let n = AS_Anno.senAttr g
      c = Map.findWithDefault (error "Config not found!") n $ configsMap s
  in Goal { gName = n, gStatus = genericConfigToGStatus c }) $ goalsList s
