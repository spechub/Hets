{- |
Module      :  $Header$
Description :  Gtk Generic Prover GUI.
Copyright   :  (c) Thiemo Wiedemeyer, Uni Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  raider@informatik.uni-bremen.de
Stability   :  provisional
Portability :  needs POSIX

Generic Gtk GUI for automatic theorem provers.
-}

module GUI.GtkGenericATP ( genericATPgui ) where

import Graphics.UI.Gtk
import Graphics.UI.Gtk.Glade

import GUI.GtkUtils
import qualified GUI.Glade.GenericATP as GenericATP

import Interfaces.GenericATPState

import Control.Concurrent (forkIO, killThread, yield)
import Control.Concurrent.MVar
import Control.Monad (unless, when)

import Common.AS_Annotation as AS_Anno
import Common.Result
import Common.Utils (getEnvSave, readMaybe)

import Proofs.BatchProcessing

import Data.List
import Data.Maybe (fromMaybe, fromJust)
import qualified Data.Map as Map

import Logic.Prover

genericATPgui :: (Ord proof_tree, Ord sentence)
              => ATPFunctions sign sentence mor proof_tree pst
              -- ^ prover specific functions
              -> Bool -- ^ prover supports extra options
              -> String -- ^ prover name
              -> String -- ^ theory name
              -> Theory sign sentence proof_tree -- ^ theory consisting of a
                 -- signature and a list of Named sentence
              -> [FreeDefMorphism sentence mor] -- ^ freeness constraints
              -> proof_tree -- ^ initial empty proof_tree
              -> IO [ProofStatus proof_tree] -- ^ proof status for each goal
genericATPgui atpFun hasEOptions prName thName th freedefs pt = do
  result <- newEmptyMVar
  postGUIAsync $ do
    xml              <- getGladeXML GenericATP.get
    -- get objects
    window           <- xmlGetWidget xml castToWindow "GenericATP"
    -- buttons at buttom
    btnClose         <- xmlGetWidget xml castToButton "btnClose"
    btnHelp          <- xmlGetWidget xml castToButton "btnHelp"
    btnSaveConfig    <- xmlGetWidget xml castToButton "btnSaveConfig"
    -- goal list
    trvGoals         <- xmlGetWidget xml castToTreeView "trvGoals"
    -- options area
    sbTimeout        <- xmlGetWidget xml castToSpinButton "sbTimeout"
    entryOptions     <- xmlGetWidget xml castToEntry "entryOptions"
    cbIncludeProven  <- xmlGetWidget xml castToCheckButton "cbIncludeProven"
    cbSaveBatch      <- xmlGetWidget xml castToCheckButton "cbSaveBatch"
    -- prove buttons
    btnStop          <- xmlGetWidget xml castToButton "btnStop"
    btnProveSelected <- xmlGetWidget xml castToButton "btnProveSelected"
    btnProveAll      <- xmlGetWidget xml castToButton "btnProveAll"
    -- status and axioms
    lblStatus        <- xmlGetWidget xml castToLabel "lblStatus"
    trvAxioms        <- xmlGetWidget xml castToTreeView "trvAxioms"
    -- info and save buttons
    btnSaveProblem   <- xmlGetWidget xml castToButton "btnSaveProblem"
    btnShowDetails   <- xmlGetWidget xml castToButton "btnShowDetails"

    windowSetTitle window $ prName ++ ": " ++ thName

    let widgets = [toWidget entryOptions | hasEOptions] ++
                  [ toWidget btnClose        , toWidget btnShowDetails
                  , toWidget btnHelp         , toWidget btnSaveConfig
                  , toWidget sbTimeout
                  , toWidget cbIncludeProven , toWidget btnProveSelected
                  , toWidget btnProveSelected, toWidget btnProveAll
                  , toWidget lblStatus       , toWidget btnSaveProblem ]
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
    listGoals <- setListData trvGoals show $ toGoals initState
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
                e@('.':_) -> e
                e -> '.':e
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
          let (nGoal,lp') = prepareLP (proverState s) s g inclProven
          prob <- goalOutput atpFun lp' nGoal $ createProverOptions atpFun
                    $ getConfig prName g pt $ configsMap s
          textView (prName ++ " Problem for Goal " ++ g) prob
            $ Just (thName ++ '_':g ++ ext)
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
              detailsText = concatMap ('\n':) output
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
          let (nGoal,lp') = prepareLP (proverState s) s g inclProven
              cfg = configsMap s
          switch False
          forkIOWithPostProcessing
            (runProver atpFun lp'(getConfig prName g pt cfg) False thName nGoal)
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
              update' s'
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
        let firstGoalName = head $ filter (flip Map.member openGoalsMap)
                              $ map AS_Anno.senAttr $ goalsList s
            opts = words opts'
            afterEachProofAttempt gPSF nSen nextSen cfg@(retval,_) = do
              cont <- goalProcessed stateMVar timeout opts numGoals prName
                                    gPSF nSen False cfg
              case retval of
                ATPError m -> errorDialog "Error" m
                _ -> return ()
              postGUISync $ do
                s' <- readMVar stateMVar
                update' s'
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
      else widgetShow window

  -- waiting for results
  res <- takeMVar result
  -- diags should not be plainly shown by putStrLn here
  maybe (fail "reverse translation of names failed") return res

  where
    prepareLP prS s g' inclProven =
      let goals = goalsList s
          cfg = configsMap s
          idx = fromMaybe (error "Goal not found!")
                  $ findIndex ((==g') . AS_Anno.senAttr) goals
          (beforeThis, afterThis) = splitAt idx goals
          g = head afterThis -- Why use head and not goal?
          proved = filter (checkGoal cfg . AS_Anno.senAttr) beforeThis
      in if inclProven
        then (g, foldl (\ lp provedGoal -> atpInsertSentence atpFun lp
                            (provedGoal { AS_Anno.isAxiom = True }))
                          prS $ reverse proved)
        else (g, prS)

saveConfigCurrent :: (Ord proof_tree)
                  => GenericState sign sentence proof_tree pst -> proof_tree
                  -> String -> SpinButton -> Entry
                  -> IO (GenericState sign sentence proof_tree pst)
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

-- | Updates the display of the status of the current goal.
update :: GenericState sign sentence proof_tree pst -> TreeView
       -> ListStore Goal -> ListStore String -> Label -> SpinButton -> Entry
       -> IO ()
update s trvGoals listGoals listAxioms lblStatus sbTimeout entryOptions = do
  -- update goal list
  oldGoals' <- listStoreToList listGoals
  let newGoals = goalsList s
      oldGoals = foldl (\ gs g -> (g, length gs):gs) [] oldGoals'
  mapM_ (\ g' -> do
      let n = AS_Anno.senAttr g'
          (g, idx) = fromMaybe (error "Goal not found!")
                        $ find (\ (Goal { gName = n' }, _) -> n == n') oldGoals
          c = Map.findWithDefault (error "Config not found!") n $ configsMap s
      listStoreSetValue listGoals idx $ g { gStatus = genericConfigToGStatus c }
    ) newGoals

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

toGoals :: GenericState sign sentence proof_tree pst -> [Goal]
toGoals s = map (\ g ->
  let n = AS_Anno.senAttr g
      c = Map.findWithDefault (error "Config not found!") n $ configsMap s
  in Goal { gName = n, gStatus = genericConfigToGStatus c }) $ goalsList s
