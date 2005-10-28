{- |
Module      :  $Header$
Description :  Goal management GUI.
Copyright   :  (c) Rene Wagner, Klaus Lüttich, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  needs POSIX

Goal management GUI for the structured level similar to how 'SPASS.Prove'
works for SPASS.

-}

{- ToDo:

  - grey out GUI while waiting for Prover
  - remove warnings
-}

module GUI.ProofManagement where

import Control.Exception

import Logic.Prover

import qualified Common.AS_Annotation as AS_Anno
import Common.PrettyPrint
import qualified Common.Lib.Pretty as Pretty
import Common.PPUtils
import Common.ProofUtils
import Common.Utils
import qualified Common.Result as Result
import Common.GlobalAnnotations
import Data.List
import Data.Maybe
import Data.IORef
import qualified Control.Exception as Exception
import qualified Control.Concurrent as Concurrent

import HTk
import SpinButton
import DialogWin
import TextDisplay
import Separator
import Space
import XSelection

import GUI.HTkUtils

import qualified Common.Lib.Map as Map
import qualified Common.OrderedMap as OMap

import Proofs.GUIState
import Logic.Logic
import Logic.Grothendieck
import Logic.Prover
import qualified Comorphisms.KnownProvers as KnownProvers
import qualified Static.DevGraph as DevGraph

-- debugging
import Debug.Trace

-- * Proof Management GUI

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

{- |
  Converts a 'ProofGUIState' into a ('ProverStatusColour', 'String') tuple to be
  displayed by the GUI.
-}
toGuiStatus :: ProofGUIState lid sentence
            -> (ProverStatusColour, String)
toGuiStatus st = if proverRunning st
  then statusRunning
  else statusNotRunning

{- |
  Generates a list of 'GUI.HTkUtils.LBGoalView' representations of all goals
  from a 'SPASS.Prove.State'.

  Uses 'toStatusIndicator' internally.
-}
goalsView :: ProofGUIState lid sentence  -- ^ current global state
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

-- TODO: for every element of goals perform a lookup on thSen to retrieve the associated BasicProof
--       map that using GUI.HTkUtils.indicatorFromBasicProof and pass it to GUI.HTkUtils.populateGoalsListBox

-- ** GUI Implementation

-- *** Utility Functions

{- |
  Populates the "Pick Theorem Prover" 'ListBox' with prover names (or possibly
  paths to provers).
-}
populatePathsListBox :: ListBox String
                     -> KnownProvers.KnownProversMap
		     -> IO ()
populatePathsListBox lb provers = do
  lb # HTk.value (Map.keys provers)
  return ()

-- *** Callbacks

{- |
   Updates the display of the status of the selected goals.
-}
updateDisplay :: ProofGUIState lid sentence -- ^ current global state
              -> Bool -- ^ set to 'True' if you want the 'ListBox' to be updated
              -> ListBox String -- ^ 'ListBox' displaying the status of all goals (see 'goalsView')
              -> ListBox String -- ^ 'ListBox' displaying possible morphism paths to prover logics
              -> Label -- ^ 'Label' displaying the status of the currently selected goal(s)
              -> IO ()
updateDisplay st updateLb goalsLb pathsLb statusLabel = do
    -- update goals listbox
    when updateLb
         (populateGoalsListBox goalsLb (goalsView st))
    -- set selected Prover
    let ind = if (isJust $ selectedProver st) 
              then findIndex (==(fromJust $ selectedProver st)) 
                       $ Map.keys (proversMap st)
              else Nothing
    when (isJust ind)
         (selection (fromJust ind) pathsLb >> return ())
    -- update status label
    let (color, label) = toGuiStatus st
    statusLabel # text label
    statusLabel # foreground (show color)
    return () 

{- |
  Called whenever the button "Select All" is clicked.
-}
doSelectAllGoals :: ProofGUIState lid sentence
		 -> ListBox String
                 -> IO (ProofGUIState lid sentence)
doSelectAllGoals s@(ProofGUIState {theory = DevGraph.G_theory _ _ thSen}) lb = 
  do
  let s' = s{selectedGoals = goals}
  -- FIXME: this will probably blow up if the number of goals isn't constant
  mapM_ (\n -> selection n lb) (map snd (zip goals ([0..]::[Int])))
  return s'
  where
    goals = OMap.keys (goalMap s)

{- |
  Called whenever a goal is selected from the goals 'ListBox'
-}
doSelectGoal :: ProofGUIState lid sentence
             -> ListBox String
	     -> IO (ProofGUIState lid sentence)
doSelectGoal s lb = do
  sel <- (getSelection lb) :: IO (Maybe [Int])
  -- FIXME: this will probably blow up if the number of goals isn't constant
  let selGoals = maybe ([]) (map (goals!!)) sel
      s' = s{selectedGoals = selGoals}
  return s'
  where goals = OMap.keys (goalMap s)

{- |
  Called whenever the button "Display" is clicked.
-}
doDisplayGoals ::
    (Logic  lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
            sign1 morphism1 symbol1 raw_symbol1 proof_tree1) =>
       ProofGUIState lid1 sentence1
    -> IO () 
doDisplayGoals s@(ProofGUIState { theoryName = thName
                                , theory=DevGraph.G_theory lid1 sig1 _}) = 
    do sens' <- DevGraph.coerceThSens (logicId s) lid1 "" sens
       createTextSaveDisplay ("Selected Goals from Theory " ++ thName) 
                          (thName ++ "-goals.txt") (goalsText sens')
    where goalsText s' = show $ 
                      vsep (map (print_named lid1 emptyGlobalAnnos 
                                 . AS_Anno.mapNamed (simplify_sen lid1 sig1)) 
                                           $ toNamedList s')
          sens = selectedGoalMap s

{- |
  Called whenever the button "Show proof details" is clicked.
-}
doShowProofDetails :: 
    (Logic lid
           sublogics1
           basic_spec1
           sentence
           symb_items1
           symb_map_items1
           sign1
           morphism1
           symbol1
           raw_symbol1
           proof_tree1) => 
       ProofGUIState lid sentence
    -> IO ()
doShowProofDetails s@(ProofGUIState { theoryName = thName
                                , theory=DevGraph.G_theory lid1 sig1 _}) = 
     createTextSaveDisplay ("Proof Details of Selected Goals from Theory " 
                            ++ thName) 
                           (thName ++ "-proof-details.txt") (detailsText sens)
    where sens = selectedGoalMap s
          detailsText s' = show $ 
                      vsep (map (\ (l,st) -> Pretty.text l Pretty.$$ 
                                            Pretty.nest 4 (printSenStat st)) $ 
                            OMap.toList s')
          printSenStat st = 
              if null $ thmStatus st
                 then stat "Open"
                 else Pretty.vcat $ 
                      map printCmWStat $ 
                      sortBy (comparing snd) $ thmStatus st
          stat s = Pretty.text "Status:" Pretty.<+> Pretty.text s
          printCmWStat (c,bp) =
              Pretty.text "Com:" Pretty.<+> Pretty.text (show c) Pretty.$$
              Pretty.nest 4 (printBP bp)
          printBP bp = case bp of
                       DevGraph.BasicProof _ ps -> 
                           case ps of
                           Open _ -> stat "Open"
                           Disproved _ -> stat "Disproved"
                           Proved _ uaxs pr _ _ -> 
                               stat "Proved" 
                               Pretty.$$ Pretty.text "Used axioms:" Pretty.<+> 
                               Pretty.fsep (Pretty.punctuate 
                                                  Pretty.comma
                                                  (map (Pretty.text 
                                                        . show) 
                                                       uaxs)) 
                               Pretty.$$ Pretty.text "Prover:" Pretty.<+> 
                               Pretty.text pr

                       x -> stat (show x)


{- |
  Called whenever a prover is selected from the "Pick Theorem Prover" ListBox.
-}
doSelectProverPath :: ProofGUIState lid sentence
		   -> ListBox String
                   -> IO (ProofGUIState lid sentence)
doSelectProverPath s lb = 
    do selected <- (getSelection lb) :: IO (Maybe [Int]) 
       return (s {selectedProver = 
                      maybe Nothing 
                            (\ (x:_) -> Just (Map.keys (proversMap s) !! x)) 
                            selected
                 })
-- TODO: retrieve selected index from lb, look that up in the list of known
--       provers, and save the prover name in selectedProver


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
    -> (   ProofGUIState lid sentence 
        -> IO (Result.Result (ProofGUIState lid sentence)))
    -- ^ called whenever the "Prove" button is clicked
    -> (   ProofGUIState lid sentence 
        -> IO (Result.Result (ProofGUIState lid sentence)))
    -- ^ called whenever the "More fine grained selection" button is clicked
    -> String -- ^ theory name
    -> DevGraph.G_theory -- ^ theory
    -> KnownProvers.KnownProversMap -- ^ map of known provers
    -> [(G_prover,AnyComorphism)] -- ^ list of suitable comorphisms to provers 
                       -- for sublogic of G_theory
    -> IO (Result.Result DevGraph.G_theory)
proofManagementGUI lid proveF fineGrainedSelectionF 
                   thName th@(DevGraph.G_theory _ _ thSen) 
                   knownProvers comorphList = 
  do
  -- KnownProvers.showKnownProvers knownProvers
  -- initial backing data structure
  initState <- initialState lid thName th knownProvers comorphList
  stateRef <- newIORef initState

  -- main window
  main <- createToplevel [text $ thName ++ " - Select Goal(s) and Prove"]
  pack main [Expand On, Fill Both]

  -- VBox for the whole window
  b <- newVBox main []
  pack b [Expand On, Fill Both]

  -- HBox for the upper part (goals on the left, options/results on the right)
  b2 <- newHBox b []
  pack b2 [Expand On, Fill Both]

  -- left frame (goals)
  left <- newFrame b2 []
  pack left [Expand On, Fill Both]

  b3 <- newVBox left []
  pack b3 [Expand On, Fill Both]

  l0 <- newLabel b3 [text "Goals:"]
  pack l0 [Anchor NorthWest]

  lbFrame <- newFrame b3 []
  pack lbFrame [Expand On, Fill Both]

  lb <- newListBox lbFrame [bg "white",exportSelection False,
                            selectMode Multiple, 
                            height 15] :: IO (ListBox String)
  populateGoalsListBox lb (goalsView initState)
  pack lb [Expand On, Side AtLeft, Fill Both]
  sb <- newScrollBar lbFrame []
  pack sb [Expand On, Side AtRight, Fill Y]
  lb # scrollbar Vertical sb

  selectAllButton <- newButton b3 [text "Select all"]
  pack selectAllButton [Expand Off, Fill None, Anchor SouthEast]

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

  l3 <- newLabel rvb [text "Pick Theorem Prover:"]
  pack l3 [Anchor NorthWest]

  rhb3 <- newHBox rvb []
  pack rhb3 [Expand On, Fill Both]

  hsp3 <- newLabel rhb3 [text hindent]
  pack hsp3 []

  pathsFrame <- newFrame rhb3 []
  pack pathsFrame []
  pathsLb <- newListBox pathsFrame [HTk.value $ ([]::[String]), bg "white",
                                    selectMode Single, exportSelection False,
                                    height 4, width 28] :: IO (ListBox String)
  populatePathsListBox pathsLb knownProvers
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

  -- bottom frame (close button)
  bottom <- newFrame b []
  pack bottom [Expand Off, Fill Both]
  
  closeButton <- newButton bottom [text "Close"]
  pack closeButton [Expand Off, Fill None, Side AtRight]

  updateDisplay initState False lb pathsLb statusLabel

  -- events
  (selectGoal, _) <- bindSimple lb (ButtonPress (Just 1))
  selectAllGoals <- clicked selectAllButton
  (selectProverPath, _) <- bindSimple pathsLb (ButtonPress (Just 1))
  displayGoals <- clicked displayGoalsButton
  moreProverPaths <- clicked moreButton
  doProve <- clicked proveButton
  showProofDetails <- clicked proofDetailsButton
  close <- clicked closeButton

  -- event handlers
  spawnEvent 
    (forever
      ((selectGoal >>> do
          s <- readIORef stateRef
	  s' <- doSelectGoal s lb
	  writeIORef stateRef s'
          done)
      +> (selectAllGoals >>> do
            s <- readIORef stateRef
	    s' <- doSelectAllGoals s lb
	    writeIORef stateRef s'
            done)
      +> (displayGoals >>> do
            s <- readIORef stateRef
	    doDisplayGoals s
            done)
      +> (selectProverPath>>> do
            s <- readIORef stateRef
	    s' <- doSelectProverPath s pathsLb
	    writeIORef stateRef s'
            done)
      +> (moreProverPaths >>> do
            s <- readIORef stateRef
	    let s' = s{proverRunning = True}
	    updateDisplay s' True lb pathsLb statusLabel
	    Result.Result ds ms'' <- fineGrainedSelectionF s
            s'' <- case ms'' of
                   Nothing -> fail "fineGrainedSelection returned Nothing"
                   Just x -> return x
	    let s''' = s'' {proverRunning = False,accDiags = accDiags s'' ++ ds}
	    updateDisplay s''' True lb pathsLb statusLabel
	    writeIORef stateRef s'''
            done)
      +> (doProve >>> do
            s <- readIORef stateRef
	    let s' = s{proverRunning = True}
	    updateDisplay s' True lb pathsLb statusLabel
	    Result.Result ds ms'' <- proveF s'
            s'' <- case ms'' of
                   Nothing -> fail "proveF returned Nothing"
                   Just x -> return x
	    let s''' = s''{proverRunning = False,accDiags = accDiags s'' ++ ds}
	    updateDisplay s''' True lb pathsLb statusLabel
	    writeIORef stateRef s'''
            done)
      +> (showProofDetails >>> do
            s <- readIORef stateRef
	    doShowProofDetails s
            done)
      ))
  sync (close >>> destroy main)

  -- read the global state back in
  s <- readIORef stateRef
  case theory s of
   DevGraph.G_theory lidT sigT sensT -> 
    do gMap <- DevGraph.coerceThSens (logicId s) lidT "" (goalMap s)
       return (Result.Result {Result.diags = accDiags s, 
                              Result.maybeResult = 
                                  Just (DevGraph.G_theory lidT sigT 
                                                    (Map.union sensT gMap))
                             }
              )
  -- TODO: do something with the resulting G_theory before returning it?

