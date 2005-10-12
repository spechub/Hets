{- |
Module      :  $Header$
Description :  Goal management GUI.
Copyright   :  (c) Rene Wagner, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rwagner@tzi.de
Stability   :  provisional
Portability :  needs POSIX

Goal management GUI for the structured level similar to how 'SPASS.Prove'
works for SPASS.

-}

module GUI.ProofManagement where

import Control.Exception

import Logic.Prover

import Common.AS_Annotation
import Common.PrettyPrint
import Common.ProofUtils

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

import GUI.HTkUtils

import qualified Common.Lib.Map as Map

-- debugging
import Debug.Trace

-- * Proof Management GUI

-- ** Backing Data Structures 

{- |
  Represents the global state of the prover GUI.
-}
data State = State { -- | currently selected goal or Nothing
                     selectedGoals :: [String],
		     -- | whether a prover is running or not
		     proverRunning :: Bool
                   }

{- |
  Creates an initial State.
-}
initialState :: GUI.ProofManagement.State
initialState = 
    State {selectedGoals = [],
           proverRunning = False }

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
  Converts a 'GUI.ProofManagement.State' into a ('ProverStatusColour', 'String') tuple to be
  displayed by the GUI.
-}
toGuiStatus :: GUI.ProofManagement.State
            -> (ProverStatusColour, String)
toGuiStatus st = if proverRunning st
  then statusRunning
  else statusNotRunning

{- |
  Converts a 'Proof_status' into a short 'GUI.HTkUtils.LBStatusIndicator' to be
  displayed by the GUI in a 'ListBox'.
-}
toStatusIndicator :: (Proof_status a) -- ^ status to convert
                  -> LBStatusIndicator
toStatusIndicator st = case st of
  Proved _ _ _ _ _ -> LBIndicatorProved
  Disproved _ -> LBIndicatorDisproved
  _ -> LBIndicatorOpen

{- |
  Generates a list of 'GUI.HTkUtils.LBGoalView' representations of all goals
  from a 'SPASS.Prove.State'.

  Uses 'toStatusIndicator' internally.
-}
goalsView :: GUI.ProofManagement.State  -- ^ current global state
          -> [LBGoalView] -- ^ resulting ['LBGoalView'] list
goalsView _ = []

-- ** GUI Implementation

-- *** Utility Functions

-- *** Callbacks

{- |
   Updates the display of the status of the selected goals.
-}
updateDisplay :: GUI.ProofManagement.State -- ^ current global state
              -> Bool -- ^ set to 'True' if you want the 'ListBox' to be updated
              -> ListBox String -- ^ 'ListBox' displaying the status of all goals (see 'goalsView')
              -> ListBox String -- ^ 'ListBox' displaying possible morphism paths to prover logics
              -> Label -- ^ 'Label' displaying the status of the currently selected goal(s)
              -> IO ()
updateDisplay st updateLb goalsLb pathsLb statusLabel = do
    -- update goals listbox
    when updateLb
         (populateGoalsListBox goalsLb (goalsView st))
    -- update status label
    let (color, label) = toGuiStatus st
    statusLabel # text label
    statusLabel # foreground (show color)
    return () 

-- *** Main GUI

{- |
  Invokes the GUI.
-}
proofManagementGUI :: IO() -- ^ nothing
proofManagementGUI = do
  -- initial backing data structure
  let initState = initialState
  stateRef <- newIORef initState

  -- main window
  main <- createToplevel [text $ "Select Goal(s) and Prove"]
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

  lb <- newListBox lbFrame [bg "white",
                            selectMode Multiple, height 15] :: IO (ListBox String)
  populateGoalsListBox lb (goalsView initState)
  pack lb [Expand On, Side AtLeft, Fill Both]
  sb <- newScrollBar lbFrame []
  pack sb [Expand On, Side AtRight, Fill Y]
  lb # scrollbar Vertical sb

  -- right frame (options/results)
  right <- newFrame b2 []
  pack right [Expand On, Fill Both, Anchor NorthWest]

  spacer <- newLabel right [text "   "]
  grid spacer [GridPos (0,1), Sticky W, Sticky W]

  l1 <- newLabel right [text "Selected Goal(s):"]
  grid l1 [GridPos (0,0), Columnspan 4, Sticky W]

  displayGoalsButton <- newButton right [text "Display"]
  grid displayGoalsButton [GridPos (4,1), Sticky E]

  l2 <- newLabel right [text "Choose Prover:"]
  grid l2 [GridPos (1,2), Columnspan 3, Sticky W]

  pathsFrame <- newFrame right []
  grid pathsFrame [GridPos (2,3), Columnspan 3]
  pathsLb <- newListBox pathsFrame [value $ ([]::[String]), bg "white",
                                      selectMode Single, height 6, width 40] :: IO (ListBox String)
  pack pathsLb [Expand On, Side AtLeft, Fill Both]
  pathsSb <- newScrollBar pathsFrame []
  pack pathsSb [Expand On, Side AtRight, Fill Y]
  pathsLb # scrollbar Vertical pathsSb

  moreButton <- newButton right [text "More..."]
  grid moreButton [GridPos (3,4), Sticky E]

  proveButton <- newButton right [text "Prove"]
  grid proveButton [GridPos (4,4), Sticky E]

  l3 <- newLabel right [text "Status:"]
  grid l3 [GridPos (1,5), Sticky W]

  statusLabel <- newLabel right [text (snd statusNotRunning)]
  grid statusLabel [GridPos (2,5), Columnspan 2, Sticky W]

  l4 <- newLabel right [text "Details:"]
  grid l4 [GridPos (1,6), Sticky W]

  proofDetailsButton <- newButton right [text "Show Proof Details"]
  grid proofDetailsButton [GridPos (3,6), Columnspan 2, Sticky E]

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

  -- events
  (selectGoal, _) <- bindSimple lb (ButtonPress (Just 1))
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
	  putStrLn "goal selected"
          done)
      +> (displayGoals >>> do
            s <- readIORef stateRef
	    putStrLn "display clicked"
            done)
      +> (selectProverPath>>> do
            s <- readIORef stateRef
	    putStrLn "proverPath selected"
            done)
      +> (moreProverPaths >>> do
            s <- readIORef stateRef
	    putStrLn "more clicked"
            done)
      +> (doProve >>> do
            s <- readIORef stateRef
	    putStrLn "prove clicked"
            done)
      +> (showProofDetails >>> do
            s <- readIORef stateRef
	    putStrLn "proof details clicked"
            done)
      ))
  sync (close >>> destroy main)

  -- read the global state back in
  s <- readIORef stateRef

  -- TODO: do something with the results

  return ()

