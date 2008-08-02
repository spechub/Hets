{- |
Module      :  $Header$
Description :  Goal management GUI.
Copyright   :  (c) Rene Wagner, Klaus Lüttich, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  needs POSIX

Goal management GUI for the structured level similar to how 'SPASS.Prove'
works for SPASS.
-}

module GUI.ProofManagement (proofManagementGUI,GUIMVar) where

import Common.AS_Annotation as AS_Anno
import qualified Common.Doc as Pretty
import qualified Common.Result as Result
import qualified Data.Map as Map
import qualified Common.OrderedMap as OMap
import Common.ExtSign

import Data.List

import qualified Control.Concurrent as Conc
import HTk
import Separator
import Space
import XSelection

import GUI.HTkUtils
import GUI.ProofDetails

import Proofs.AbstractState
import Logic.Comorphism
import Logic.Logic
import Logic.Prover
import qualified Comorphisms.KnownProvers as KnownProvers
import Static.GTheory

-- debugging
-- import Debug.Trace

-- * Proof Management GUI

-- ** some types

-- | Type for storing the proof management window
type GUIMVar = Conc.MVar (Maybe Toplevel)

-- ** Defining the view

{- |
  Colors used by the GUI to indicate the status of a goal.
-}
data ProverStatusColour
  -- | Not running
  = Black
  -- | Running
  | Blue
   deriving (Bounded,Enum,Show)

data SelButtonFrame = SBF { selAllEv :: Event ()
                          , deselAllEv :: Event ()
                          , sbf_btns :: [Button]
                          , sbf_btnFrame :: Frame}

data SelAllListbox = SAL SelButtonFrame (ListBox String)

{- |
  Generates a ('ProverStatusColour', 'String') tuple.
-}
statusNotRunning :: (ProverStatusColour, String)
statusNotRunning = (Black, "No Prover Running")

{- |
  Generates a ('ProverStatusColour', 'String') tuple.
-}
statusRunning :: (ProverStatusColour, String)
statusRunning = (Blue, "Waiting for Prover")

{- | Converts a 'ProofState' into a ('ProverStatusColour',
     'String') tuple to be displayed by the GUI.
-}
toGuiStatus :: ProofState lid sentence
            -> (ProverStatusColour, String)
toGuiStatus st = if proverRunning st
  then statusRunning
  else statusNotRunning

{- |
  Generates a list of 'GUI.HTkUtils.LBGoalView' representations of all goals
  from a 'SPASS.Prove.State'.

  Uses a status indicator internally.
-}
goalsView :: ProofState lid sentence  -- ^ current global state
          -> [LBGoalView] -- ^ resulting ['LBGoalView'] list
goalsView = map toStatus . OMap.toList . goalMap
    where toStatus (l,st) =
              let tStatus = thmStatus st
                  si = if null tStatus
                       then LBIndicatorOpen
                       else indicatorFromBasicProof
                                (maximum $ map snd $ tStatus)
              in LBGoalView { statIndicator = si
                            , goalDescription = l}

-- ** GUI Implementation

-- *** Utility Functions

{- |
  Populates the "Pick Theorem Prover" 'ListBox' with prover names (or possibly
  paths to provers).
-}
populatePathsListBox :: ListBox String
                     -> KnownProvers.KnownProversMap
                     -> IO ()
populatePathsListBox lb prvs = do
  lb # HTk.value (Map.keys prvs)
  return ()

populateAxiomsList ::
    (Logic  lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
            sign1 morphism1 symbol1 raw_symbol1 proof_tree1) =>
       ListBox String
    -> ProofState lid1 sentence1
    -> IO ()
populateAxiomsList lbAxs s =
    do aM' <- axiomMap s
       lbAxs # HTk.value (map (\(k,sen) -> if (wasTheorem sen) then "(Th) "++k
                                           else k) $
                              OMap.toList aM')
       return ()

setSelectedProver :: ListBox String
                  -> ProofState lid1 sentence1
                  -> IO ()
setSelectedProver lb st = do
    let ind = case selectedProver st of
              Just sp -> findIndex (==sp) $ Map.keys (proversMap st)
              Nothing -> Nothing
    maybe (return ()) (\i -> selection i lb >> return ()) ind

-- *** Callbacks

{- |
   Updates the display of the status of the selected goals.
-}
updateDisplay :: ProofState lid sentence -- ^ current global state
    -> Bool
    -- ^ set to 'True' if you want the 'ListBox' to be updated
    -> ListBox String
    -- ^ 'ListBox' displaying the status of all goals (see 'goalsView')
    -> ListBox String
    -- ^ 'ListBox' displaying possible morphism paths to prover logics
    -> Label
    -- ^ 'Label' displaying the status of the currently selected goal(s)
    -> IO ()
updateDisplay st updateLb goalsLb pathsLb statusLabel = do
    -- update goals listbox
    when updateLb
         (do
           (offScreen,_) <- view Vertical goalsLb
           populateGoalsListBox goalsLb (goalsView st)
           moveto Vertical goalsLb offScreen)
    setSelectedProver pathsLb st
    -- update status label
    let (color, label) = toGuiStatus st
    statusLabel # text label
    statusLabel # foreground (show color)
    return ()

updateStateGetSelectedGoals ::
    (Logic  lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
            sign1 morphism1 symbol1 raw_symbol1 proof_tree1) =>
           ProofState lid1 sentence1
        -> ListBox String
        -> IO (ProofState lid1 sentence1)
updateStateGetSelectedGoals s lb =
    do sel <- (getSelection lb) :: IO (Maybe [Int])
       return (s {selectedGoals =
                      maybe [] (map ((OMap.keys (goalMap s))!!)) sel})

updateStateGetSelectedSens ::
    (Logic  lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
            sign1 morphism1 symbol1 raw_symbol1 proof_tree1) =>
           ProofState lid1 sentence1
        -> ListBox String -- ^ axioms listbox
        -> ListBox String -- ^ theorems listbox
        -> IO (ProofState lid1 sentence1)
updateStateGetSelectedSens s lbAxs lbThs =
    do aM <- axiomMap s
       selA <- (getSelection lbAxs) :: IO (Maybe [Int])
       selT <- (getSelection lbThs) :: IO (Maybe [Int])
       return (s { includedAxioms   = maybe [] (fil aM) selA
                 , includedTheorems = maybe [] (fil (goalMap s)) selT })
    where fil str = map ((OMap.keys str)!!)

{- |
 Depending on the first argument all entries in a ListBox are selected
  or deselected
-}

doSelectAllEntries :: Bool -- ^ indicates wether all entries should be selected
                         -- or deselected
                 -> ListBox a
                 -> IO ()
doSelectAllEntries selectAll lb =
  if selectAll
     then selectionRange (0::Int) EndOfText lb >> return ()
     else clearSelection lb

{- |
  Called whenever the button "Display" is clicked.
-}
doDisplayGoals ::
    (Logic  lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
            sign1 morphism1 symbol1 raw_symbol1 proof_tree1) =>
       ProofState lid1 sentence1
    -> IO ()
doDisplayGoals s =
    case theory s of
      G_theory lid1 (ExtSign sig1 _) _ _ _ -> do
       let thName = theoryName s
           goalsText s' = show $ Pretty.vsep $
                          map (print_named lid1 .
                               AS_Anno.mapNamed (simplify_sen lid1 sig1)) $
                          toNamedList s'
           sens = selectedGoalMap s
       sens' <- coerceThSens (logicId s) lid1 "" sens
       createTextSaveDisplay ("Selected Goals from Theory " ++ thName)
                          (thName ++ "-goals.txt") (goalsText sens')

{- |
  Called whenever a prover is selected from the "Pick Theorem Prover" ListBox.
-}
doSelectProverPath :: ProofState lid sentence
                   -> ListBox String
                   -> IO (ProofState lid sentence)
doSelectProverPath s lb =
    do selected <- (getSelection lb) :: IO (Maybe [Int])
       return (s {selectedProver =
                      maybe Nothing
                            (\ (index:_) ->
                                 Just (Map.keys (proversMap s) !! index))
                            selected
                 })

newSelectButtonsFrame :: (Container par) =>
                         par -> IO SelButtonFrame
newSelectButtonsFrame b3 =
  do
  selFrame <- newFrame b3 []
  pack selFrame [Expand Off, Fill None, Side AtLeft, Anchor SouthWest]

  selHBox <- newHBox selFrame []
  pack selHBox [Expand Off, Fill None, Anchor West]

  selectAllButton <- newButton selHBox [text "Select all"]
  pack selectAllButton [Expand Off, Fill None]

  deselectAllButton <- newButton selHBox [text "Deselect all"]
  pack deselectAllButton [Expand Off, Fill None]
  -- events
  selectAll <- clicked selectAllButton
  deselectAll <- clicked deselectAllButton

  return (SBF { selAllEv = selectAll
              , deselAllEv = deselectAll
              , sbf_btns = [deselectAllButton,selectAllButton]
              , sbf_btnFrame = selFrame })

newExtSelListBoxFrame :: (Container par) =>
                         par -> String -> Distance
                      -> IO SelAllListbox
newExtSelListBoxFrame b2 title hValue =
  do
  left <- newFrame b2 []
  pack left [Expand On, Fill Both]

  b3 <- newVBox left []
  pack b3 [Expand On, Fill Both]

  l0 <- newLabel b3 [text title]
  pack l0 [Anchor NorthWest]

  lbFrame <- newFrame b3 []
  pack lbFrame [Expand On, Fill Both, Anchor NorthWest]

  lb <- newListBox lbFrame [bg "white",exportSelection False,
                            selectMode Multiple,
                            height hValue] :: IO (ListBox String)

  pack lb [Expand On, Side AtLeft, Fill Both]
  sb <- newScrollBar lbFrame []
  pack sb [Expand On, Side AtRight, Fill Y, Anchor West]
  lb # scrollbar Vertical sb

  -- buttons for goal selection
  sbf <- newSelectButtonsFrame b3
  return (SAL sbf lb)


-- *** Main GUI
{- |
  Invokes the GUI.
-}
proofManagementGUI ::
  (Logic lid sublogics1
             basic_spec1
             sentence
             symb_items1
             symb_map_items1
             sign1
             morphism1
             symbol1
             raw_symbol1
             proof_tree1) =>
     lid
  -> ProofActions lid sentence -- ^ record of possible GUI actions
  -> String -- ^ theory name
  -> String -- ^ warning information
  -> G_theory -- ^ theory
  -> KnownProvers.KnownProversMap -- ^ map of known provers
  -> [(G_prover,AnyComorphism)] -- ^ list of suitable comorphisms to provers
                                -- for sublogic of G_theory
  -> GUIMVar -- ^ allows only one Proof window per graph;
             {- must be filled with Nothing and is filled with Nothing after
                closing the window; while the window is open it is filled with
                the Toplevel -}
    -> IO (Result.Result G_theory)
proofManagementGUI lid prGuiAcs
                   thName warningTxt th
                   knownProvers comorphList guiMVar =
  do
  -- KnownProvers.showKnownProvers knownProvers
  -- initial backing data structure
  initState <- (initialState lid thName th knownProvers comorphList
                >>= recalculateSublogicF prGuiAcs)
  stateMVar <- Conc.newMVar initState
  lockMVar <- Conc.newMVar ()
  -- main window
  main <- createToplevel [text $ thName ++ " - Select Goal(s) and Prove"]
  Conc.tryTakeMVar guiMVar >>= (\ mmt ->
         let err s = fail $ "ProofManagementGUI: ("++s++") MVar must be "++
                      "filled with Nothing when entering proofManagementGUI"
         in do
            maybe (err "not filled")
                  (maybe (Conc.putMVar guiMVar $ Just main)
                         (const $ err "filled with (Just x)"))
                  mmt)
  -- VBox for the whole window
  b <- newVBox main []
  pack b [Expand On, Fill Both]
  -- HBox for the upper part (goals on the left, options/results on the right)
  b2 <- newHBox b []
  pack b2 [Expand On, Fill Both]
  -- ListBox for goal selection
  (SAL (SBF { selAllEv = selectAllGoals
            , deselAllEv = deselectAllGoals
            , sbf_btns = goalBtns
            , sbf_btnFrame = goalsBtnFrame}) lb)
      <- newExtSelListBoxFrame b2 "Goals:" 14
  -- button to select only the open goals
  selectOpenGoalsButton <- newButton goalsBtnFrame [text "Select open goals"]
  pack selectOpenGoalsButton [Expand Off, Fill None, Side AtLeft]
  -- right frame (options/results)
  right <- newFrame b2 []
  pack right [Expand On, Fill Both, Anchor NorthWest]
  let hindent = "   "
  let vspacing = cm 0.2
  rvb <- newVBox right []
  pack rvb [Expand On, Fill Both]

  l1 <- newLabel rvb [text "Selected Goal(s):"]
  pack l1 [Anchor NorthWest]

  rhb1 <- newHBox rvb []
  pack rhb1 [Expand On, Fill Both]

  hsp1 <- newLabel rhb1 [text hindent]
  pack hsp1 []

  displayGoalsButton <- newButton rhb1 [text "Display"]
  pack displayGoalsButton []

  proveButton <- newButton rhb1 [text "Prove"]
  pack proveButton []

  proofDetailsButton <- newButton rhb1 [text "Show proof details"]
  pack proofDetailsButton []

  vsp1 <- newSpace rvb vspacing []
  pack vsp1 []

  l2 <- newLabel rvb [text "Status:"]
  pack l2 [Anchor NorthWest]

  rhb2 <- newHBox rvb []
  pack rhb2 [Expand On, Fill Both]

  hsp2 <- newLabel rhb2 [text hindent]
  pack hsp2 []

  statusLabel <- newLabel rhb2 [text (snd statusNotRunning)]
  pack statusLabel []

  vsp2 <- newSpace rvb vspacing []
  pack vsp2 []

  l3 <- newLabel rvb [text "Sublogic of Currently Selected Theory:"]
  pack l3 [Anchor NorthWest]

  rhb3 <- newHBox rvb []
  pack rhb3 [Expand On, Fill Both]

  hsp3 <- newLabel rhb3 [text hindent]
  pack hsp3 []

  sublogicLabel <- newLabel rhb3 [text (show $ sublogicOfTheory initState)]
  pack sublogicLabel []

  vsp3 <- newSpace rvb vspacing []
  pack vsp3 []

  l4 <- newLabel rvb [text "Pick Theorem Prover:"]
  pack l4 [Anchor NorthWest]

  rhb4 <- newHBox rvb []
  pack rhb4 [Expand On, Fill Both]

  hsp4 <- newLabel rhb4 [text hindent]
  pack hsp4 []

  pathsFrame <- newFrame rhb4 []
  pack pathsFrame []
  pathsLb <- newListBox pathsFrame [HTk.value $ ([]::[String]), bg "white",
                                    selectMode Single, exportSelection False,
                                    height 4, width 28] :: IO (ListBox String)
  pack pathsLb [Expand On, Side AtLeft, Fill Both]
  pathsSb <- newScrollBar pathsFrame []
  pack pathsSb [Expand On, Side AtRight, Fill Y]
  pathsLb # scrollbar Vertical pathsSb

  moreButton <- newButton rvb [text "More fine grained selection..."]
  pack moreButton [Anchor SouthEast]
  -- separator
  sp1 <- newSpace b (cm 0.15) []
  pack sp1 [Expand Off, Fill X, Side AtBottom]

  newHSeparator b

  sp2 <- newSpace b (cm 0.15) []
  pack sp2 [Expand Off, Fill X, Side AtBottom]

  -- theory composer frame (toggled with button)
  composer <- newFrame b []
  pack composer [Expand On, Fill Both]

  compBox <- newVBox composer []
  pack compBox [Expand On, Fill Both]

  newLabel compBox [text "Fine grained composition of theory:"] >>=
        (\ lab -> pack lab [])

  icomp <- newFrame compBox []
  pack icomp [Expand On, Fill Both]

  icBox <- newHBox icomp []
  pack icBox [Expand On, Fill Both]

  (SAL (SBF { selAllEv = selectAllAxs
            , deselAllEv = deselectAllAxs
            , sbf_btns = axsBtns
            , sbf_btnFrame = axiomsBtnFrame}) lbAxs)
       <- newExtSelListBoxFrame icBox "Axioms to include:" 10
  -- button to deselect axioms that are former theorems
  deselectFormerTheoremsButton <- newButton axiomsBtnFrame
                                            [text "Deselect former theorems"]
  pack deselectFormerTheoremsButton [Expand Off, Fill None, Side AtLeft]

  (SAL (SBF { selAllEv = selectAllThs
            , deselAllEv = deselectAllThs
            , sbf_btns = thsBtns}) lbThs)
      <- newExtSelListBoxFrame icBox "Theorems to include if proven:" 10
  -- separator
  spac1 <- newSpace b (cm 0.15) []
  pack spac1 [Expand Off, Fill X, Side AtBottom]

  newHSeparator b

  spac2 <- newSpace b (cm 0.15) []
  pack spac2 [Expand Off, Fill X, Side AtBottom]
  -- bottom frame (close button)
  bottom <- newFrame b []
  pack bottom [Expand Off, Fill Both]

  bottomThFrame <- newFrame bottom []
  pack bottomThFrame [Expand Off, Fill Both, Side AtLeft]

  showThButton <- newButton bottomThFrame [text "Show theory"]
  pack showThButton [Expand Off, Fill None, Side AtLeft]

  showSelThButton <- newButton bottomThFrame [text "Show selected theory"]
  pack showSelThButton [Expand Off, Fill None, Side AtRight]

  closeButton <- newButton bottom [text "Close"]
  pack closeButton [Expand Off, Fill None, Side AtRight,PadX (pp 13)]
  -- put the labels in the listboxes
  populateGoalsListBox lb (goalsView initState)
  populateAxiomsList lbAxs initState
  populatePathsListBox pathsLb (proversMap initState)
  lbThs # HTk.value (OMap.keys (goalMap initState))
  doSelectAllEntries True lb
  doSelectAllEntries True lbAxs
  doSelectAllEntries True lbThs
  updateDisplay initState False lb pathsLb statusLabel
  let goalSpecificWids = map EnW [displayGoalsButton,proveButton,
                                  proofDetailsButton,moreButton]
      wids = [EnW pathsLb,EnW lbThs,EnW lb,EnW lbAxs] ++
             map EnW (selectOpenGoalsButton : closeButton : showThButton :
                      showSelThButton : deselectFormerTheoremsButton :
                      axsBtns++goalBtns++thsBtns) ++
             goalSpecificWids
  enableWidsUponSelection lb goalSpecificWids
  pack main [Expand On, Fill Both]
  putWinOnTop main
  let updateStatusSublogic s = do
        sWithSel <- (updateStateGetSelectedSens s lbAxs lbThs >>=
                     (\ si -> updateStateGetSelectedGoals si lb))
        s' <- recalculateSublogicF prGuiAcs $
                (sWithSel {proversMap = knownProvers})
        let newSublogicText = show $ sublogicOfTheory s'
        sublogicText <- getText sublogicLabel
        when (sublogicText /= newSublogicText)
             (sublogicLabel # text newSublogicText >> return ())
        when (Map.keys (proversMap s) /= Map.keys (proversMap s'))
             (do populatePathsListBox pathsLb (proversMap s')
                 setSelectedProver pathsLb s')
        return s'{ selectedProver =
                       maybe Nothing
                             (\ sp -> find (==sp) $ Map.keys (proversMap s'))
                             (selectedProver s')}
  -- events
  (selectProverPath, _) <- bindSimple pathsLb (ButtonPress (Just 1))
  (selectGoals, _) <- bindSimple lb (ButtonPress (Just 1))
  (selectAxioms, _) <- bindSimple lbAxs (ButtonPress (Just 1))
  (selectTheorems, _) <- bindSimple lbThs (ButtonPress (Just 1))
  selectOpenGoals <- clicked selectOpenGoalsButton
  deselectFormerTheorems <- clicked deselectFormerTheoremsButton
  displayGoals <- clicked displayGoalsButton
  moreProverPaths <- clicked moreButton
  doProve <- clicked proveButton
  showProofDetails <- clicked proofDetailsButton
  close <- clicked closeButton
  showTh <- clicked showThButton
  showSelTh <- clicked showSelThButton
  (closeWindow,_) <- bindSimple main Destroy
  -- event handlers
  spawnEvent
    (forever
      (  (selectGoals >>> do
            Conc.modifyMVar_ stateMVar updateStatusSublogic
            enableWidsUponSelection lb goalSpecificWids
            done)
      +> (selectAxioms >>> do
            Conc.modifyMVar_ stateMVar updateStatusSublogic
            done)
      +> (selectTheorems >>> do
            Conc.modifyMVar_ stateMVar updateStatusSublogic
            done)
      +> (selectOpenGoals >>> do
             s <- Conc.takeMVar stateMVar
             clearSelection lb
             let isOpenGoal (_,st) =
                     let thst = thmStatus st
                     in if null thst
                        then True
                        else case maximum $ map snd $ thst of
                             BasicProof _ pst ->
                                 case goalStatus pst of
                                 Open -> True
                                 _ -> False
                             _ -> False
             mapM_ (\ i -> selection i lb)
                   (findIndices isOpenGoal $ OMap.toList $ goalMap s)
             enableWidsUponSelection lb goalSpecificWids
             s' <- updateStatusSublogic s
             Conc.putMVar stateMVar s'
             done)
      +> (deselectFormerTheorems >>> do
            s <- Conc.takeMVar stateMVar
            aM <- axiomMap s
            let axiomList = OMap.toList aM
                isNotFormerTheorem (_,st) = not $ wasTheorem st
            sel <- (getSelection lbAxs) :: IO (Maybe [Int])
            clearSelection lbAxs
            mapM_ (\ i -> selection i lbAxs) $
                  maybe [] (filter (isNotFormerTheorem . (!!) axiomList)) sel
            s' <- updateStatusSublogic s
            Conc.putMVar stateMVar s'
            done)
      +> (deselectAllGoals >>> do
            doSelectAllEntries False lb
            disableWids goalSpecificWids
            Conc.modifyMVar_ stateMVar updateStatusSublogic
            done)
      +> (selectAllGoals >>> do
            doSelectAllEntries True lb
            enableWids goalSpecificWids
            Conc.modifyMVar_ stateMVar updateStatusSublogic
            done)
      +> (selectAllAxs >>> do
            doSelectAllEntries True lbAxs
            Conc.modifyMVar_ stateMVar updateStatusSublogic
            done)
      +> (selectAllThs >>> do
            doSelectAllEntries True lbThs
            Conc.modifyMVar_ stateMVar updateStatusSublogic
            done)
      +> (deselectAllAxs >>> do
            doSelectAllEntries False lbAxs
            Conc.modifyMVar_ stateMVar updateStatusSublogic
            done)
      +> (deselectAllThs >>> do
            doSelectAllEntries False lbThs
            Conc.modifyMVar_ stateMVar updateStatusSublogic
            done)
      +> (displayGoals >>> do
            s <- Conc.readMVar stateMVar
            s' <- updateStateGetSelectedGoals s lb
            doDisplayGoals s'
            done)
      +> (selectProverPath>>> do
            Conc.modifyMVar_ stateMVar (\ s ->
                       doSelectProverPath s pathsLb)
            done)
      +> (moreProverPaths >>> do
            s <- Conc.readMVar stateMVar
            let s' = s{proverRunning = True}
            updateDisplay s' True lb pathsLb statusLabel
            disableWids wids
            prState <- updateStatusSublogic s'
            Result.Result ds ms'' <- (fineGrainedSelectionF prGuiAcs) prState
            s'' <- case ms'' of
                   Nothing -> do
                       putStrLn "fineGrainedSelection returned Nothing"
                       Result.printDiags 2 ds
                       return s'
                   Just res -> return res
            let s''' = s'' { proverRunning = False
                           , accDiags = accDiags s'' ++ ds }
            enableWids wids
            updateDisplay s''' True lb pathsLb statusLabel
            putWinOnTop main
            Conc.tryTakeMVar stateMVar -- ensure that MVar is empty
            Conc.putMVar stateMVar s'''
            done)
      +> (doProve >>> do
            s <- Conc.takeMVar stateMVar
            let s' = s{proverRunning = True}
            updateDisplay s' True lb pathsLb statusLabel
            disableWids wids
            prState <- updateStatusSublogic s'
            Result.Result ds ms'' <- (proveF prGuiAcs) prState
            s'' <- case ms'' of
                   Nothing -> do
                       putStrLn "proveF returned Nothing"
                       Result.printDiags 2 ds
                       return s'
                   Just res -> return res
            let s''' = s''{proverRunning = False,
                           accDiags = accDiags s'' ++ ds}
            Conc.putMVar stateMVar s'''
            mv <- Conc.tryTakeMVar lockMVar
            case mv of
                Nothing -> done
                Just _  -> do
                  enable lb
                  updateDisplay s''' True lb pathsLb statusLabel
                  enableWids wids
                  putWinOnTop main
                  Conc.tryPutMVar lockMVar ()
                  done)
      +> (showProofDetails >>> do
            s <- Conc.readMVar stateMVar
            s' <- updateStateGetSelectedGoals s lb
            doShowProofDetails s'
            done)
      +> (showTh >>> do
            displayTheoryWithWarning "Theory" thName warningTxt th
            done)
      +> (showSelTh >>> do
            s <- Conc.readMVar stateMVar
            displayTheoryWithWarning "Selected Theory" thName warningTxt
              (selectedTheory s)
            done)
      ))
  sync ( (close >>> destroy main)
      +> (closeWindow >>> Conc.takeMVar lockMVar)
       )
  -- clean up locking of window
  Conc.tryTakeMVar guiMVar >>= (\ mmt ->
         let err s = fail $ "ProofManagementGUI: ("++s++") MVar must be "++
                      "filled with Nothing when entering proofManagementGUI"
         in do
            maybe (err "not filled")
                  (maybe (err "filled with Nothing")
                         (const $ Conc.putMVar guiMVar Nothing))
                  mmt)
  -- read the global state back in
  s <- Conc.takeMVar stateMVar
  case theory s of
   G_theory lidT sigT indT sensT _ ->
    do gMap <- coerceThSens (logicId s) lidT
                               "ProofManagement last coerce" (goalMap s)
       return (Result.Result {Result.diags = accDiags s,
                              Result.maybeResult =
                                  Just (G_theory lidT sigT indT
                                        (Map.union sensT gMap) startThId)
                             }
              )
