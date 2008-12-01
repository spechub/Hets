{- |
Module      :  $Header$
Description :  Consistency Checker GUI.
Copyright   :  (c) Rainer Grabbe, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rainer@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (uses uni, needs POSIX)

Generic GUI for consistency checker. Based upon genericATP GUI.
-}

module GUI.ConsistencyChecker (ccgui) where

import Common.Utils (getEnvSave)

import Data.List
import Data.Maybe (isJust)
import qualified Control.Exception as Exception
import qualified Control.Concurrent as Conc

import GHC.Read

import HTk
import SpinButton
import Separator
import XSelection
import Space
import ScrollBar

import GUI.Utils
import Interfaces.GenericATPState

-- ** Constants

{- |
  Default time limit for the GUI mode prover in seconds.
-}
guiDefaultTimeLimit :: Int
guiDefaultTimeLimit = 10

-- ** Defining the view

{- |
  Colors used by the GUI to indicate the status of a spec.
-}
data CheckStatusColour
  -- | Consistent
  = Green
  -- | Time-consistent
  | Brown
  -- | Inconsistent
  | Red
  -- | Not checked
  | Black
  -- | Running
  | Blue
   deriving (Bounded,Enum,Show)

{- |
  Generates a ('CheckStatusColour', 'String') tuple representing a consistent
  specification status.
-}
statusConsistent :: (CheckStatusColour, String)
statusConsistent = (Green, "Consistent")

{- |
  Generates a ('CheckStatusColour', 'String') tuple representing a time
  consistentProved specification status.
-}
statusTConsistent :: (CheckStatusColour, String)
statusTConsistent = (Brown, "t-consistent")

{- | Generates a ('CheckStatusColour', 'String') tuple representing an
  inconsistent specification status.  -}
statusInconsistent :: (CheckStatusColour, String)
statusInconsistent = (Red, "Inconsistent")

{- |
  Generates a ('CheckStatusColour', 'String') tuple representing an open (not
  yet checked) specification status.
-}
statusNotChecked :: (CheckStatusColour, String)
statusNotChecked = (Black, "Not checked")

{- |
  Generates a ('CheckStatusColour', 'String') tuple representing a running
  specification status.
-}
statusRunning :: (CheckStatusColour, String)
statusRunning = (Blue, "Running")

{- | stores widgets of an options frame and the frame itself -}
data OpFrame = OpFrame
    { of_Frame :: Frame
    , of_timeSpinner :: SpinButton
    , of_timeEntry :: Entry Int
    , of_optionsEntry :: Entry String }

-- * GUI Implementation

-- ** Utility Functions

{- |
  Retrieves the value of the time limit 'Entry'. Ignores invalid input.
-}
getValueSafe :: Int -- ^ default time limt
             -> Entry Int -- ^ time limit 'Entry'
             -> IO Int -- ^ user-requested time limit or default in case of a
                       -- parse error
getValueSafe defaultTimeLimit timeEntry =
    Exception.catchJust Exception.userErrors ((getValue timeEntry) :: IO Int)
                  (const $ return defaultTimeLimit)

-- | Text displayed by the batch mode window.
batchInfoText :: Int -- ^ batch time limt
              -> Int -- ^ total number of goals
              -> Int -- ^ number of that have been processed
              -> String
batchInfoText tl gTotal gDone =
  let totalSecs = (gTotal - gDone) * tl
      (remMins,secs) = divMod totalSecs 60
      (hours,mins) = divMod remMins 60
  in
  "Batch mode running.\n" ++
  show gDone ++ "/" ++ show gTotal ++ " goals processed.\n" ++
  "At most " ++ show hours ++ "h " ++ show mins ++ "m " ++ show secs ++
  "s remaining."

-- ** Callbacks

{- |
 Depending on the first argument all entries in a ListBox are selected
  or deselected
-}
doSelectAllEntries :: Bool -- ^ indicates wether all entries should be selected
                           -- or deselected
                   -> ListBox a -> IO ()
doSelectAllEntries selectAll lb =
    if selectAll then selectionRange (0 :: Int) EndOfText lb >> return () else
        clearSelection lb

-- !! updateDisplay
newOptionsFrame :: Container par =>
                par -- ^ the parent container
             -> (Entry Int -> Spin -> IO a)
             -- ^ Function called by pressing one spin button
             -> Bool -- ^ extra options input line
             -> IO OpFrame
newOptionsFrame con updateFn isExtraOps = do
  right <- newFrame con []

  -- contents of newOptionsFrame
  l1 <- newLabel right [text "Options:"]
  pack l1 [Anchor NorthWest]
  opFrame <- newFrame right []
  pack opFrame [Expand On, Fill X, Anchor North]

  spacer <- newLabel opFrame [text "   "]
  pack spacer [Side AtLeft]

  opFrame2 <- newVBox opFrame []
  pack opFrame2 [Expand On, Fill X, Anchor NorthWest]

  timeLimitFrame <- newFrame opFrame2 []
  pack timeLimitFrame [Expand On, Fill X, Anchor West]

  l2 <- newLabel timeLimitFrame [text "TimeLimit"]
  pack l2 [Side AtLeft]

  -- extra HBox for time limit display
  timeLimitLine <- newHBox timeLimitFrame []
  pack timeLimitLine [Expand On, Side AtRight, Anchor East]

  (timeEntry :: Entry Int) <- newEntry timeLimitLine [width 18,
                                              HTk.value guiDefaultTimeLimit]
  pack timeEntry []

  timeSpinner <- newSpinButton timeLimitLine (updateFn timeEntry) []
  pack timeSpinner []

  l3 <- newLabel opFrame2 [text "Extra Options:"]
  when isExtraOps $
       pack l3 [Anchor West]
  (optionsEntry :: Entry String) <- newEntry opFrame2 [width 37]
  when isExtraOps $
       pack optionsEntry [Fill X, PadX (cm 0.1)]

  return OpFrame
    { of_Frame = right
    , of_timeSpinner = timeSpinner
    , of_timeEntry = timeEntry
    , of_optionsEntry = optionsEntry }

-- ** Main GUI

{- |
  Invokes the consistency checker GUI. Users may start the batch prover run on
  all goals, or use a detailed GUI for proving each goal manually.
-}
ccgui :: IO ()
ccgui = do
  -- create initial backing data structure
  -- !! test value
  let batchTLimit = (20 :: Integer)

  -- !! test stub
  let specName = "Foo bar spec name"

-- !! still need to know why the left listbox is too small in
-- x-direction (has too much space)

  -- main window
  main <- createToplevel [text $ specName ++ " - Concistency Checker"]
  pack main [Expand On, Fill Both]

  -- VBox for the whole window
  b <- newVBox main []
  pack b [Expand On, Fill Both]

  -- HBox for the upper part (specs on the left, options/results on the right)
  b2 <- newHBox b []
  pack b2 [Expand On, Fill Both]

  left <- newVBox b2 []
  pack left [Expand On, Fill Both]

  l0 <- newLabel left [text "Specifications:"]
  pack l0 [Anchor NorthWest]

  lbFrame <- newFrame left []
  pack lbFrame [Expand On, Fill Both]

  lb <- newListBox lbFrame
     [ bg "white"
     , exportSelection False
     , selectMode Multiple, height 15] :: IO (ListBox String)
  pack lb [Expand On, Side AtLeft, Fill Both]
  sb <- newScrollBar lbFrame []
  pack sb [Expand On, Side AtRight, Fill Y, Anchor West]
  lb # scrollbar Vertical sb
  lb # HTk.value ["1", "2", "7", "33"] -- !! test

  selHBox <- newHBox left []
  pack selHBox [Expand Off, Fill None, Anchor West]

  selectAllButton <- newButton selHBox [text "Select all"]
  pack selectAllButton []
  deselectAllButton <- newButton selHBox [text "Deselect all"]
  pack deselectAllButton []

  selectUncheckedButton <- newButton left
      [text "Select unchecked specifications"]
  pack selectUncheckedButton [Anchor West]

  right <- newVBox b2 []
  pack right [Expand Off, Fill Y, Anchor NorthWest]

  -- !! some functionality is still missing. ;)
  -- right frame (options/results)
  OpFrame { of_Frame = opRight
          , of_timeSpinner = timeSpinner
          , of_timeEntry = timeEntry
          , of_optionsEntry = optionsEntry}
      <- newOptionsFrame right
                 (\ timeEntry sp -> synchronize main
                   (return ()
                    ))
                 True
  pack opRight [Expand Off, Fill Both]

  -- buttons for options
  buttonsHb1 <- newHBox right []
  pack buttonsHb1 [Anchor NorthEast]

  saveCheckButton <- newButton buttonsHb1 [text $ "Save check info"]
  pack saveCheckButton []
  stopButton <- newButton buttonsHb1 [text "Stop"]
  pack stopButton []
  runButton <- newButton buttonsHb1 [text "Check"]
  pack runButton []

  let vspacing = cm 0.2

  -- status lines
  stBox <- newVBox right []
  pack stBox [Fill X]

  l1 <- newLabel stBox [text "Status:"]
  pack l1 [Anchor West]
  statusLabel <- newLabel stBox [text "(dummy) current state"]
  pack statusLabel [Anchor West, PadX (cm 0.5)]

  vsp1 <- newSpace stBox vspacing []
  pack vsp1 []

  l2 <- newLabel stBox [text "Sublogic of currently selected specifications:"]
  pack l2 [Anchor West]
  sublogicLabel <- newLabel stBox [text "(dummy) some sublogic"]
  pack sublogicLabel [Anchor West, PadX (cm 0.5)]

  vsp2 <- newSpace stBox vspacing []
  pack vsp2 []

  l3 <- newLabel stBox [text "Current specification"]
  pack l3 [Anchor West]
  specLabel <- newLabel stBox [text "(dummy) some spec"]
  pack specLabel [Anchor West, PadX (cm 0.5)]

  vsp3 <- newSpace stBox vspacing []
  pack vsp3 []

  -- consistency checker frame
  conCheckFrame <- newFrame right []
  pack conCheckFrame [Fill Both, Anchor NorthWest]
  l4 <- newLabel conCheckFrame
     [text ("Select a specific consistency checker:")]
  pack l4 [Anchor West]

  conCheckIFrame <- newFrame conCheckFrame []
  pack conCheckIFrame [Fill Both, Anchor NorthWest, PadX (cm 0.5)]

  conCheckLb <- newListBox conCheckIFrame
     [ HTk.value ([] :: [String])
     , bg "white"
     , exportSelection False
     , selectMode Browse
     , height 4 ] :: IO (ListBox String)
  pack conCheckLb [Expand On, Fill Both, Side AtLeft]
  conCheckSb <- newScrollBar conCheckIFrame []
  pack conCheckSb [Fill Y, Side AtRight]
  conCheckLb # scrollbar Vertical conCheckSb

  moreButton <- newButton right [text "More fine grained selection..."]
  pack moreButton [Side AtBottom, Anchor East]

  -- separator
  sp1_1 <- newSpace b (cm 0.15) []
  pack sp1_1 [Expand Off, Fill X, Side AtBottom]

  newHSeparator b

  sp1_2 <- newSpace b (cm 0.15) []
  pack sp1_2 [Expand Off, Fill X, Side AtBottom]

  -- bottom frame (help/show/exit buttons)
  bottom <- newHBox b []
  pack bottom [Expand Off, Fill Both]

  helpButton <- newButton bottom [text "Help"]
  pack helpButton [PadX (cm 0.3), IPadX (cm 0.1)]
  showSumButton <- newButton bottom [text "Show summary"]
  pack showSumButton [PadX (cm 0.3)]
  exitButton <- newButton bottom [text "Close"]
  pack exitButton [PadX (cm 0.3), IPadX (cm 0.1)]


{-
  saveCheckButton <- newButton buttonsHb1 [text $ "Save check info"]
  pack saveCheckButton []
  stopButton <- newButton buttonsHb1 [text "Stop"]
  pack stopButton []
  runButton <- newButton buttonsHb1 [text "Check"]
-}

  let specWids = map EnW [saveCheckButton, runButton, moreButton]
      wids = [EnW lb, EnW conCheckLb] ++ specWids ++ map EnW
             [ selectAllButton
             , deselectAllButton
             , selectUncheckedButton
             , helpButton
             , showSumButton
             , exitButton ]

  enableWidsUponSelection lb specWids
  disable stopButton
  putWinOnTop main

  -- MVars for thread-safe communication
  mVar_batchId <- Conc.newEmptyMVar :: IO (Conc.MVar Conc.ThreadId)
  windowDestroyedMVar <- Conc.newEmptyMVar :: IO (Conc.MVar ())

  --events
  (selectGoal, _) <- bindSimple lb (ButtonPress (Just 1))
  selectAll <- clicked selectAllButton
  deselectAll <- clicked deselectAllButton
  selectUnchecked <- clicked selectUncheckedButton

  runCheck <- clicked runButton
  stopCheck <- clicked stopButton

  help <- clicked helpButton
  showSummary <- clicked showSumButton
  exit <- clicked exitButton

  (closeWindow,_) <- bindSimple main Destroy

  -- event handlers (much to do!!)

-- !! mvars missing
  spawnEvent
    (forever
      ((selectGoal >>> do
           enableWidsUponSelection lb specWids
           done)
      +> (help >>> do
            createTextDisplay ("Help")
                              ("No help available yet.")
                              [size (80, 30)]
            done)
      +> (showSummary >>> do
            createTextSaveDisplay
                ("Status Summary of all checked specifications")
                ("dummy.file")
                ("nothing yet")
            done)
      +> (deselectAll >>> do
            doSelectAllEntries False lb
            disableWids specWids
            done)

      +> (selectAll >>> do
            doSelectAllEntries True lb
            enableWids specWids
            done)
      +> (runCheck >>> do
            disableWids wids
            enable stopButton
            done)
      +> (stopCheck >>> do
            enableWids wids
            disable stopButton
            done)
      ))

  sync ( (exit >>> destroy main)
      +> (closeWindow >>> do
                 destroy main)
       )
