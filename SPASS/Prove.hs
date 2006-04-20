{- |
Module      :  Prove.hs
Description :  Interface for the SPASS theorem prover.
Copyright   :  (c) Rene Wagner, Klaus Lüttich, Rainer Grabbe, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rainer25@tzi.de
Stability   :  provisional
Portability :  needs POSIX

Interface for the SPASS theorem prover, uses GUI.GenericATP.
See <http://spass.mpi-sb.mpg.de/> for details on SPASS.

-}

{- 
    todo:

      - exclude graphical interface into genericATP
      
      - rework output of saveConfiguration

      - window opens too small on linux; why? ... maybe fixed
      --> failure still there, opens sometimes too small (using KDE),
          but not twice in a row

      - keep focus of listboxes if updated (also relevant for 
        in GUI.ProofManagement)

      - check if the theorem is used in the proof; 
        if not, the theory is inconsistent; 
        mark goal as proved and emmit a warning...

      - Implement a consistency checker based on GUI

-}

module SPASS.Prove (spassProver,spassProveGUI,spassProveBatch) where

import Logic.Prover

import SPASS.Sign
import SPASS.Conversions
import SPASS.ProveHelp
import SPASS.Translate
import SPASS.Print (genSPASSProblem)

import qualified Common.AS_Annotation as AS_Anno
import Common.ProofUtils
import Common.PrettyPrint 

import ChildProcess
import ProcessClasses

import Text.Regex
import Data.List
import Data.Maybe
import Data.IORef
import qualified Control.Exception as Exception
import qualified Control.Concurrent as Concurrent

import GHC.Read
import System
import System.IO.Error

import HTk
import SpinButton
import Messages
import TextDisplay
import Separator
import XSelection
import Space

import GUI.HTkUtils
-- import GUI.GenericATP

import qualified Common.Lib.Map as Map

-- debugging
import Debug.Trace

-- * Prover implementation

{- |
  The Prover implementation. First runs the batch prover (with graphical
  feedback), then starts the GUI prover.
-}
spassProver :: Prover Sign Sentence ()
spassProver =
  Prover { prover_name = "SPASS",
           prover_sublogic = "SPASS",
           prove = spassProveGUI
         }

-- * Shared data structures and assorted utility functions

{- |
  Represents a prover configuration used when proving a goal.
-}
data SPASSConfig = SPASSConfig { 
    -- | time limit in seconds passed 
    -- to SPASS via -TimeLimit. Default will be used if Nothing.
    timeLimit :: Maybe Int,
    -- | True if timelimit exceed during last prover run
    timeLimitExceeded :: Bool,
    -- | extra options passed verbatimely to SPASS. 
    -- -DocProof, -Stdin, and -TimeLimit will be overridden.
    extraOpts :: [String],
    -- | Represents the result of a prover run.
    proof_status :: Proof_status (),
    resultOutput :: [String]
                               } deriving (Eq, Ord, Show)

{- |
  Creates an empty SPASSConfig with a given goal name.
  Default time limit, no resultOutput and no extra options.
-}
emptyConfig :: String -> SPASSConfig
emptyConfig n = SPASSConfig {timeLimit = Nothing,
                             timeLimitExceeded = False,
                             extraOpts = [],
                             proof_status = openSPASSProof_status n,
                             resultOutput = []
                            }

openSPASSProof_status :: String -> Proof_status ()
openSPASSProof_status n = openProof_status n (prover_name spassProver) () 

{- |
  Utility function to set the time limit of a SPASSConfig.
  For values <= 0 a default value is used.
-}
setTimeLimit :: Int -> SPASSConfig -> SPASSConfig
setTimeLimit n c = if n > 0 then c{timeLimit = Just n} 
                   else c{timeLimit = Nothing}

{- |
  Utility function to set the extra options of a SPASSConfig.
-}
setExtraOpts :: [String] -> SPASSConfig -> SPASSConfig
setExtraOpts opts c = c{extraOpts = opts}

{- |
  Represents the general return value of a prover run.
-}
data SpassProverRetval
  -- | SPASS completed successfully
  = SpassSuccess
  -- | SPASS did not terminate before the time limit exceeded
  | SpassTLimitExceeded
  -- | an error occured while running SPASS
  | SpassError String
  deriving (Eq, Show)

{- |
  Checks whether a SpassProverRetval indicates that the time limit was
  exceeded.
-}
isTimeLimitExceeded :: SpassProverRetval -> Bool
isTimeLimitExceeded SpassTLimitExceeded = True
isTimeLimitExceeded _ = False

-- * GUI Prover

-- ** Constants

{- |
  Default time limit for the GUI mode prover in seconds.
-}
guiDefaultTimeLimit :: Int
guiDefaultTimeLimit = 10

-- ** Data Structures

{- |
  We need to store one SPASSConfig per goal.
-}
type SPASSConfigsMap = Map.Map SPIdentifier SPASSConfig

{- |
  Adjusts the configuration associated to a goal by applying the supplied
  function or inserts a new emptyConfig with the function applied if there's
  no configuration associated yet.

  Uses Map.member, Map.adjust, and Map.insert for the corresponding tasks
  internally.
-}
adjustOrSetConfig :: (SPASSConfig -> SPASSConfig) 
                     -- ^ function to be applied against the current 
                     -- configuration or a new emptyConfig
                  -> SPIdentifier -- ^ name of the goal
                  -> SPASSConfigsMap -- ^ current SPASSConfigsMap
                  -> SPASSConfigsMap 
                  -- ^ resulting SPASSConfigsMap with the changes applied
adjustOrSetConfig f k m = if (Map.member k m)
                            then Map.adjust f k m
                            else Map.insert k (f $ emptyConfig k) m

{- |
  Performs a lookup on the ConfigsMap. Returns the config for the goal or an
  empty config if none is set yet.
-}
getConfig :: SPIdentifier -> SPASSConfigsMap -> SPASSConfig
getConfig spid m = if (isJust lookupId)
                     then fromJust lookupId
                     else emptyConfig spid
  where
    lookupId = Map.lookup spid m

{- |
  Map to SPASS compliant identifiers
-}
type SPASSGoalNameMap = Map.Map String String

{- |
  Represents the global state of the prover GUI.
-}
data State = State { -- | currently selected goal or Nothing
                     currentGoal :: Maybe SPIdentifier,
                     -- | theory to work on
                     theory :: Theory Sign Sentence (),
                     -- | stores the prover configurations for each goal
                     -- and the results retrieved by running 
                     -- SPASS for each goal
                     configsMap :: SPASSConfigsMap,
                     -- | stores a mapping to SPASS compliant 
                     -- identifiers for all goals
                     namesMap :: SPASSGoalNameMap,
                     -- | list of all goals
                     goalsList :: [AS_Anno.Named SPTerm],
                     -- | logical part without theorems
                     initialLogicalPart :: SPLogicalPart,
                     batchModeIsRunning :: Bool,
                     mainDestroyed :: Bool
                   }

data ThreadState = TSt { batchId :: Maybe Concurrent.ThreadId
                       , batchStopped :: Bool
                       }

initialThreadState :: ThreadState
initialThreadState = TSt { batchId = Nothing
                         , batchStopped = False}

{- |
  Creates an initial State around a Theory.
-}
initialState :: Theory Sign Sentence () -> SPASS.Prove.State
initialState th = 
    State {currentGoal = Nothing,
           theory = th,
           configsMap = Map.fromList $
                        map (\ g -> let gName = AS_Anno.senName g
                                    in (gName, emptyConfig gName)) goals,
           namesMap = collectNameMapping nSens oSens',
           goalsList = goals,
           initialLogicalPart = foldl insertSentence 
                                      (signToSPLogicalPart sign) 
                                      (reverse axioms),
           batchModeIsRunning = False,
           mainDestroyed = False
          }
    where Theory sign oSens = th
          oSens' = toNamedList oSens
          nSens = prepareSenNames transSenName oSens'
          (axioms, goals) = partition AS_Anno.isAxiom nSens

-- ** Defining the view

{- |
  Colors used by the GUI to indicate the status of a goal.
-}
data ProofStatusColour
  -- | Proved
  = Green
  -- | Proved, but theory is inconsitent
  | Brown
  -- | Disproved
  | Red
  -- | Open
  | Black
  -- | Running
  | Blue  
   deriving (Bounded,Enum,Show)

{- |
  Generates a ('ProofStatusColour', 'String') tuple representing a Proved proof
  status.
-}
statusProved :: (ProofStatusColour, String)
statusProved = (Green, "Proved")

statusProvedButInconsistent :: (ProofStatusColour, String)
statusProvedButInconsistent = (Brown, "Proved (Theory inconsistent!)")

{- |
  Generates a ('ProofStatusColour', 'String') tuple representing a Disproved
  proof status.
-}
statusDisproved :: (ProofStatusColour, String)
statusDisproved = (Red, "Disproved")

{- |
  Generates a ('ProofStatusColour', 'String') tuple representing a Open proof
  status.
-}
statusOpen :: (ProofStatusColour, String)
statusOpen = (Black, "Open")

{- |
  Generates a ('ProofStatusColour', 'String') tuple representing a Open proof
  status in case the time limit has been exceeded.
-}
statusOpenTExceeded :: (ProofStatusColour, String)
statusOpenTExceeded = (Black, "Open (Time is up!)")

{- |
  Generates a ('ProofStatusColour', 'String') tuple representing a Running proof
  status.
-}
statusRunning :: (ProofStatusColour, String)
statusRunning = (Blue, "Running")

{- |
  Converts a 'Proof_status' into a ('ProofStatusColour', 'String') tuple to be
  displayed by the GUI.
-}
toGuiStatus :: SPASSConfig -- ^ current prover configuration
            -> (Proof_status a) -- ^ status to convert
            -> (ProofStatusColour, String)
toGuiStatus cf st = case goalStatus st of
  Proved mc -> maybe (statusProved)
                     ( \ c -> if c
                              then statusProved
                              else statusProvedButInconsistent)
                     mc
  Disproved -> statusDisproved
  _         -> if timeLimitExceeded cf
               then statusOpenTExceeded
               else statusOpen

{-| stores widgets of an options frame and the frame itself -}
data OpFrame = OpFrame { of_Frame :: Frame
                       , of_timeSpinner :: SpinButton
                       , of_timeEntry :: Entry Int
                       , of_optionsEntry :: Entry String
                       }

filterOpenGoals :: SPASSConfigsMap -> SPASSConfigsMap
filterOpenGoals = Map.filter isOpenGoal 
    where isOpenGoal cf = case (goalStatus $ proof_status cf) of
                              Open -> True
                              _    -> False


{- |
  Generates a list of 'GUI.HTkUtils.LBGoalView' representations of all goals
  from a 'SPASS.Prove.State'.
-}
goalsView :: SPASS.Prove.State  -- ^ current global prover state
          -> [LBGoalView] -- ^ resulting ['LBGoalView'] list
goalsView s = map (\ g ->
                       let cfg = Map.lookup g (configsMap s)
                           statind = maybe LBIndicatorOpen
                                       (indicatorFromProof_status . proof_status)
                                       cfg
                        in
                          LBGoalView {statIndicator = statind, 
                                      goalDescription = g})
                   (map AS_Anno.senName (goalsList s))

-- ** GUI Implementation

-- *** Utility Functions

{- |
  Retrieves the value of the time limit 'Entry'. Ignores invalid input.
-}
getValueSafe :: Int -- ^ default time limt
             -> Entry Int -- ^ time limit 'Entry'
             -> IO Int -- ^ user-requested time limit or default in case of a parse error
getValueSafe defaultTimeLimit timeEntry =
    Exception.catchJust Exception.userErrors ((getValue timeEntry) :: IO Int) 
                  (\ s -> trace ("Warning: Error "++show s++" was ignored") 
                                (return defaultTimeLimit))

{- |
  Text displayed by the batch mode window.
-}
batchInfoText :: Int -- ^ batch time limt
              -> Int -- ^ total number of goals
              -> Int -- ^ number of that have been processed
              -> String
batchInfoText tl gTotal gDone =
  let totalSecs = (gTotal - gDone) * tl
      (remMins,secs) = divMod totalSecs 60
      (hours,mins) = divMod remMins 60
  in 
  "Batch mode runnig\n"++
  show gDone ++ "/" ++ show gTotal ++ " goals processed.\n" ++
  "At most "++show hours++"h "++show mins++"m "++show secs++"s remaining."

-- *** Callbacks

{- |
  Called every time a goal has been processed in the batch mode gui.
-}
goalProcessed :: IORef SPASS.Prove.State 
               -- ^ IORef pointing to the backing State data structure
              -> Int -- ^ batch time limit
              -- -> String -- ^ extra options
              -> Int -- ^ total number of goals
              -> Label -- ^ info label
              -> Int -- ^ number of goals processed so far
              -> AS_Anno.Named SPTerm -- ^ goal that has just been processed
              -> (SpassProverRetval, SPASSConfig)
              -> IO Bool
goalProcessed stateRef tLimit numGoals label 
              processedGoalsSoFar nGoal (retval, res_cfg) = do
  s <- readIORef stateRef
  let s' = s{
      configsMap = adjustOrSetConfig 
                      (\ c -> c{timeLimitExceeded = 
                                    isTimeLimitExceeded retval,
                                timeLimit = Just tLimit,
                                proof_status = proof_status res_cfg,
                                resultOutput = resultOutput res_cfg})
                      (AS_Anno.senName nGoal) 
                      (configsMap s)}
  writeIORef stateRef s'

  let notReady = numGoals - processedGoalsSoFar > 0
  label # text (if notReady
                then (batchInfoText tLimit numGoals processedGoalsSoFar)
                else "Batch mode finished\n\n")

  return notReady

{- |
   Updates the display of the status of the current goal.
-}
updateDisplay :: SPASS.Prove.State -- ^ current global prover state
              -> Bool -- ^ set to 'True' if you want the 'ListBox' to be updated
              -> ListBox String -- ^ 'ListBox' displaying the status of all goals (see 'goalsView')
              -> Label -- ^ 'Label' displaying the status of the currently selected goal (see 'toGuiStatus')
              -> Entry Int -- ^ 'Entry' containing the time limit of the current goal
              -> Entry String -- ^ 'Entry' containing the extra options
              -> ListBox String -- ^ 'ListBox' displaying all axioms used to prove a goal (if any)
              -> IO ()
updateDisplay st updateLb goalsLb statusLabel timeEntry optionsEntry axiomsLb = do
    when updateLb
         (populateGoalsListBox goalsLb (goalsView st))
    maybe (return ())
          (\ go -> 
               let mprfst = Map.lookup go (configsMap st)
                   cf = Map.findWithDefault 
                        (error "updateDisplay: configsMap \
                               \was not initialised!!") 
                        go (configsMap st)
                   t' = maybe guiDefaultTimeLimit id (timeLimit cf)
                   opts' = unwords (extraOpts cf)
                   (color, label) = maybe statusOpen
                                    ((toGuiStatus cf) . proof_status)
                                    mprfst
                   usedAxs = maybe [] (usedAxioms . proof_status) mprfst

               in do 
                statusLabel # text label
                statusLabel # foreground (show color)
                timeEntry # HTk.value t'
                optionsEntry # HTk.value opts'
                axiomsLb # HTk.value (usedAxs::[String])
                return ()) 
          (currentGoal st)

newOptionsFrame :: Container par => 
                par -- ^ the parent container
             -> (Entry Int -> Spin -> IO a) 
             -- ^ Function called by pressing one spin button 
             -> IO OpFrame
newOptionsFrame con updateFn = do
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
  pack l3 [Anchor West]
  (optionsEntry :: Entry String) <- newEntry opFrame2 [width 37]
  pack optionsEntry [Fill X, PadX (cm 0.1)]

  return $ OpFrame { of_Frame = right                     
                   , of_timeSpinner = timeSpinner
                   , of_timeEntry = timeEntry
                   , of_optionsEntry = optionsEntry}

-- *** Main GUI

{- |
  Invokes the prover GUI. First runs the batch prover on all goals,
  then drops the user into a detailed GUI.
-}
spassProveGUI :: String -- ^ theory name
              -> Theory Sign Sentence () -- ^ theory consisting of a SPASS.Sign.Sign and a list of Named SPASS.Sign.Sentence
              -> IO([Proof_status ()]) -- ^ proof status for each goal
spassProveGUI thName th = do
  -- create initial backing data structure
  let initState = initialState th
  stateRef <- newIORef initState
  batchTLimit <- getBatchTimeLimit

  -- main window
  main <- createToplevel [text $ thName ++ " - SPASS Prover"]
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
                            selectMode Single, height 15] :: IO (ListBox String)
  populateGoalsListBox lb (goalsView initState)
  pack lb [Expand On, Side AtLeft, Fill Both]
  sb <- newScrollBar lbFrame []
  pack sb [Expand On, Side AtRight, Fill Y, Anchor West]
  lb # scrollbar Vertical sb

  -- right frame (options/results)
  OpFrame { of_Frame = right                     
          , of_timeSpinner = timeSpinner
          , of_timeEntry = timeEntry
          , of_optionsEntry = optionsEntry} 
      <- newOptionsFrame b2 
                 (\ timeEntry sp -> synchronize main
                   (do
               s <- readIORef stateRef
               maybe noGoalSelected
                     (\ goal -> 
                      do 
                      curEntTL <- getValueSafe guiDefaultTimeLimit timeEntry 
                      let sEnt = s {configsMap = 
                                        adjustOrSetConfig 
                                             (setTimeLimit curEntTL) 
                                             goal (configsMap s)}
                          cfg = getConfig goal (configsMap sEnt)
                          t = timeLimit cfg
                          t' = (case sp of
                                Up -> maybe (guiDefaultTimeLimit + 10)
                                            (+10)
                                            t
                                _ -> maybe (guiDefaultTimeLimit - 10)
                                            (\ t1 -> t1-10)
                                            t)
                          s' = sEnt {configsMap = 
                                         adjustOrSetConfig 
                                              (setTimeLimit t') 
                                              goal (configsMap sEnt)}
                      writeIORef stateRef s'
                      timeEntry # HTk.value 
                                    (maybe guiDefaultTimeLimit 
                                           id 
                                           (timeLimit $ getConfig goal $
                                                      configsMap s'))
                      done) 
                     (currentGoal s)))
  pack right [Expand On, Fill Both, Anchor NorthWest]

  -- buttons for options
  buttonsHb1 <- newHBox right []
  pack buttonsHb1 [Anchor NorthEast]

  saveDFGButton <- newButton buttonsHb1 [text "Save DFG File"]
  pack saveDFGButton [Side AtLeft]
  proveButton <- newButton buttonsHb1 [text "Prove"]
  pack proveButton [Side AtRight]

  -- result frame
  resultFrame <- newFrame right []
  pack resultFrame [Expand On, Fill Both]

  l4 <- newLabel resultFrame [text "Results:"]
  pack l4 [Anchor NorthWest]

  spacer <- newLabel resultFrame [text "   "]
  pack spacer [Side AtLeft]

  resultContentBox <- newHBox resultFrame []
  pack resultContentBox [Expand On, Anchor West, Fill Both]

  -- labels on the left side
  rc1 <- newVBox resultContentBox []
  pack rc1 [Expand Off, Anchor North]
  l5 <- newLabel rc1 [text "Status"]
  pack l5 [Anchor West]
  l6 <- newLabel rc1 [text "Used Axioms"]
  pack l6 [Anchor West]

  -- contents on the right side
  rc2 <- newVBox resultContentBox []
  pack rc2 [Expand On, Fill Both, Anchor North]

  statusLabel <- newLabel rc2 [text " -- "]
  pack statusLabel [Anchor West]
  axiomsFrame <- newFrame rc2 []
  pack axiomsFrame [Expand On, Anchor West, Fill Both]
  axiomsLb <- newListBox axiomsFrame [HTk.value $ ([]::[String]), 
                                      bg "white",exportSelection False,
                                      selectMode Browse, 
                                      height 6, width 19] :: IO (ListBox String)
  pack axiomsLb [Side AtLeft, Expand On, Fill Both]
  axiomsSb <- newScrollBar axiomsFrame []
  pack axiomsSb [Side AtRight, Fill Y, Anchor West]
  axiomsLb # scrollbar Vertical axiomsSb

  detailsButton <- newButton resultFrame [text "Show Details"]
  pack detailsButton [Anchor NorthEast]

  -- separator
  sp1 <- newSpace b (cm 0.15) []
  pack sp1 [Expand Off, Fill X, Side AtBottom]

  newHSeparator b

  sp2 <- newSpace b (cm 0.15) []
  pack sp2 [Expand Off, Fill X, Side AtBottom]

  -- batch mode frame
  batch <- newFrame b []
  pack batch [Expand Off, Fill X]

  batchTitle <- newLabel batch [text "SPASS Batch Mode:"]
  pack batchTitle [Side AtTop]

  batchLeft <- newVBox batch []
  pack batchLeft [Expand On, Fill X, Side AtLeft]

  batchBtnBox <- newHBox batchLeft []
  pack batchBtnBox [Expand On, Fill X, Side AtLeft]
  stopBatchButton <- newButton batchBtnBox [text "Stop"]
  pack stopBatchButton [] 
  runBatchButton <- newButton batchBtnBox [text "Run"]
  pack runBatchButton [] 

  batchSpacer <- newSpace batchLeft (pp 150) [orient Horizontal]
  pack batchSpacer [Side AtLeft]
  batchStatusLabel <- newLabel batchLeft [text "\n\n"]
  pack batchStatusLabel []

  OpFrame { of_Frame = batchRight
          , of_timeSpinner = batchTimeSpinner
          , of_timeEntry = batchTimeEntry
          , of_optionsEntry = batchOptionsEntry} 
      <- newOptionsFrame batch
                 (\ tEntry sp -> synchronize main
                   (do
                    curEntTL <- getValueSafe batchTLimit tEntry 
                    let t' = case sp of
                              Up -> curEntTL+10
                              _ -> max batchTLimit (curEntTL-10)
                    tEntry # HTk.value t'
                    done)) 

  pack batchRight [Expand On, Fill X, Anchor NorthWest,Side AtRight]

  batchTimeEntry # HTk.value batchTLimit

  -- separator 2
  sp1_2 <- newSpace b (cm 0.15) []
  pack sp1_2 [Expand Off, Fill X, Side AtBottom]

  newHSeparator b

  sp2_2 <- newSpace b (cm 0.15) []
  pack sp2_2 [Expand Off, Fill X, Side AtBottom]

  -- global options frame
  globalOptsFr <- newFrame b []
  pack globalOptsFr [Expand Off, Fill Both]

  gOptsTitle <- newLabel globalOptsFr [text "Global Options:"]
  pack gOptsTitle [Side AtTop]

  inclProvedThsTK <- createTkVariable True
  inclProvedThsCheckButton <- 
         newCheckButton globalOptsFr 
                        [variable inclProvedThsTK,
                         text ("include preceeding proven therorems"++
                               " in next proof attempt")]
  pack inclProvedThsCheckButton [Side AtLeft]

  -- separator 3
  sp1_3 <- newSpace b (cm 0.15) []
  pack sp1_3 [Expand Off, Fill X, Side AtBottom]

  newHSeparator b

  sp2_3 <- newSpace b (cm 0.15) []
  pack sp2_3 [Expand Off, Fill X, Side AtBottom]

  -- bottom frame (help/save/exit buttons)
  bottom <- newHBox b []
  pack bottom [Expand Off, Fill Both]

  helpButton <- newButton bottom [text "Help"]
  pack helpButton [PadX (cm 0.3), IPadX (cm 0.1)]  -- wider "Help" button
  saveButton <- newButton bottom [text "Save Prover Configuration"]
  pack saveButton [PadX (cm 0.3)]
  exitButton <- newButton bottom [text "Exit Prover"]
  pack exitButton [PadX (cm 0.3)]
  
  putWinOnTop main

  -- IORef for batch thread
  threadStateRef <- newIORef initialThreadState

  -- events
  (selectGoal, _) <- bindSimple lb (ButtonPress (Just 1))
  doProve <- clicked proveButton
  saveDFG <- clicked saveDFGButton
  showDetails <- clicked detailsButton

  runBatch <- clicked runBatchButton
  stopBatch <- clicked stopBatchButton

  help <- clicked helpButton
  saveConfiguration <- clicked saveButton
  exit <- clicked exitButton

  (closeWindow,_) <- bindSimple main Destroy

  let goalSpecificWids = [EnW timeEntry, EnW timeSpinner,EnW optionsEntry] ++ 
                         map EnW [proveButton,detailsButton,saveDFGButton]
      wids = EnW lb : goalSpecificWids ++
             [EnW batchTimeEntry, EnW batchTimeSpinner,
              EnW batchOptionsEntry,EnW inclProvedThsCheckButton] ++
             map EnW [helpButton,saveButton,exitButton,runBatchButton]

  disableWids goalSpecificWids
  disable stopBatchButton

  -- event handlers
  spawnEvent 
    (forever
      ((selectGoal >>> do
          s <- readIORef stateRef
          let oldGoal = currentGoal s
          curEntTL <- (getValueSafe guiDefaultTimeLimit timeEntry) :: IO Int
          let s' = maybe s 
                         (\ og -> s 
                             {configsMap = 
                                  adjustOrSetConfig (setTimeLimit curEntTL) 
                                                    og (configsMap s)})  
                         oldGoal
          sel <- (getSelection lb) :: IO (Maybe [Int])
          let s'' = maybe s' (\ sg -> s' {currentGoal = 
                                              Just $ AS_Anno.senName 
                                               (goalsList s' !! head sg)}) 
                             sel
          writeIORef stateRef s''
          when (isJust sel && not (batchModeIsRunning s'')) 
               (enableWids goalSpecificWids)
          when (isJust sel) $ enableWids [EnW detailsButton,EnW saveDFGButton]
          updateDisplay s'' False lb statusLabel timeEntry optionsEntry axiomsLb
          done)
      +> (saveDFG >>> do
            rs <- readIORef stateRef
            inclProvedThs <- readTkVariable inclProvedThsTK
            maybe (return ()) 
                  (\ goal -> do
                      let (nGoal,lp') = 
                              prepareLP (initialLogicalPart rs) rs 
                                        goal inclProvedThs
                      prob <- genSPASSProblem thName lp' (Just nGoal)
                      createTextSaveDisplay ("SPASS Problem for Goal "++goal) 
                                            (thName++goal++".dfg") 
                                            (showPretty prob "")
                  )
                  $ currentGoal rs
            done)
      +> (doProve >>> do
            rs <- readIORef stateRef
            if isNothing $ currentGoal rs
              then noGoalSelected
              else (do
                curEntTL <- (getValueSafe guiDefaultTimeLimit 
                                          timeEntry) :: IO Int
                inclProvedThs <- readTkVariable inclProvedThsTK
                let goal = fromJust $ currentGoal rs
                    s = rs {configsMap = adjustOrSetConfig 
                                            (setTimeLimit curEntTL) 
                                            goal 
                                            (configsMap rs)}
                    (nGoal,lp') = prepareLP (initialLogicalPart rs) rs 
                                            goal inclProvedThs
                extraOptions <- (getValue optionsEntry) :: IO String
                let s' = s {configsMap = adjustOrSetConfig 
                                            (setExtraOpts (words extraOptions))
                                            goal 
                                            (configsMap s)}
                statusLabel # text (snd statusRunning)
                statusLabel # foreground (show $ fst statusRunning)
                disableWids wids
                (retval, cfg) <- 
                    runSpass lp' (getConfig goal (configsMap s')) thName nGoal
                -- check if main is still there
                curSt <- readIORef stateRef
                if mainDestroyed curSt 
                    then done
                    else do
                 enableWids wids
                 case retval of
                   SpassError message -> errorMess message
                   _ -> return ()
                 let s'' = s'{
                     configsMap =
                        adjustOrSetConfig 
                           (\ c -> c {timeLimitExceeded = isTimeLimitExceeded retval,
                                      proof_status = proof_status cfg,
                                      resultOutput = resultOutput cfg})
                           goal (configsMap s')}
                 writeIORef stateRef s''
                 updateDisplay s'' True lb statusLabel timeEntry 
                              optionsEntry axiomsLb
                 done)
            done)
      +> (showDetails >>> do
            s <- readIORef stateRef
            if isNothing $ currentGoal s
              then noGoalSelected
              else (do
                let goal = fromJust $ currentGoal s
                let result = Map.lookup goal (configsMap s)
                let output = if isJust result
                               then resultOutput (fromJust result)
                               else ["This goal hasn't been run through "++
                                     "the prover yet."]
                let detailsText = concatMap ('\n':) output
                createTextSaveDisplay ("SPASS Output for Goal "++goal) 
                                      (goal ++ ".spass") 
                                      (seq (length detailsText) detailsText)
                done)
            done)
      +> (runBatch >>> do
            cleanupThread threadStateRef
            s <- readIORef stateRef
            -- get options for this batch run
            curEntTL <- (getValueSafe batchTLimit batchTimeEntry) :: IO Int
            let tLimit = if curEntTL > 0 then curEntTL else batchTLimit
            batchTimeEntry # HTk.value tLimit
            extOpts <- (getValue batchOptionsEntry) :: IO String
            writeIORef stateRef (s {batchModeIsRunning = True})
            let numGoals = Map.size $ filterOpenGoals $ configsMap s
            if numGoals > 0 
             then do
              batchStatusLabel # text (batchInfoText tLimit numGoals 0)
              disableWids wids
              enable stopBatchButton
              enableWidsUponSelection lb [EnW detailsButton,EnW saveDFGButton]
              enable lb
              inclProvedThs <- readTkVariable inclProvedThsTK
              batchProverId <- Concurrent.forkIO 
                   (do spassProveBatch tLimit extOpts inclProvedThs
                          (\ gPSF nSen cfg -> do 
                              cont <- goalProcessed stateRef tLimit numGoals 
                                                    batchStatusLabel 
                                                    gPSF nSen cfg
                              st <- readIORef stateRef
                              updateDisplay st True lb statusLabel timeEntry 
                                            optionsEntry axiomsLb
                              when (not cont)
                                   (do 
                                    -- putStrLn "Batch ended"
                                    disable stopBatchButton
                                    enableWids wids
                                    enableWidsUponSelection lb goalSpecificWids
                                    writeIORef stateRef 
                                            (st {batchModeIsRunning = False})
                                    cleanupThread threadStateRef)
                              return cont)
                          thName s 
                       return ())
              modifyIORef threadStateRef 
                        (\ ts -> ts{batchId = Just batchProverId})
              done
             else do
              batchStatusLabel # text ("No further open goals\n\n")
              done)
      +> (stopBatch >>> do
            cleanupThread threadStateRef
            modifyIORef threadStateRef (\ s -> s {batchStopped = True})
            -- putStrLn "Batch stopped"
            disable stopBatchButton
            enableWids wids
            enableWidsUponSelection lb goalSpecificWids
            batchStatusLabel # text "Batch mode stopped\n\n"
            st <- readIORef stateRef
            writeIORef stateRef 
                           (st {batchModeIsRunning = False})
            updateDisplay st True lb statusLabel timeEntry 
                          optionsEntry axiomsLb
            done)
      +> (help >>> do
            createTextDisplay "SPASS Help" spassHelpText [size (80, 30)]
            done)
      +> (saveConfiguration >>> do
            s <- readIORef stateRef
            let (cfgList, resList) = getCfgText $ configsMap s
                cfgText = unlines $ ("Configuration:\n":cfgList)
                                    ++ ("\nResults:\n":resList)
            createTextSaveDisplay ("SPASS Configuration for Theory " ++ thName)
                                  (thName ++ ".spcf") cfgText
            done)
      ))
  sync ( (exit >>> destroy main)
      +> (closeWindow >>> do cleanupThread threadStateRef
                             modifyIORef stateRef 
                                         (\ s -> s{mainDestroyed = True})
                             destroy main)
       )
  s <- readIORef stateRef
  let proof_stats = map (\g -> let res = Map.lookup g (configsMap s) 
                                   g' = Map.findWithDefault 
                                        (error ("Lookup of name failed: (1) "
                                                ++"should not happen \""
                                                ++g++"\""))
                                        g (namesMap s)
                                   pStat = proof_status $ fromJust res
                               in if isJust res 
                                  then transNames (namesMap s) pStat
                                  else openSPASSProof_status g') 
                    (map AS_Anno.senName $ goalsList s)
  return proof_stats
  where
    cleanupThread tRef = do
         st <- readIORef tRef
         -- cleaning up
         maybe (return ())
               (\ tId -> do 
                   Concurrent.killThread tId
                   writeIORef tRef initialThreadState)
               (batchId st)

    noGoalSelected = errorMess "Please select a goal first."
    prepareLP iLP s goal inclProvedThs =
       let (beforeThis, afterThis) = 
               splitAt (fromJust $ 
                        findIndex (\sen -> AS_Anno.senName sen == goal) 
                                  (goalsList s)) 
                       (goalsList s)
           proved = filter (\sen-> checkGoal (configsMap s) 
                                       (AS_Anno.senName sen)) beforeThis
       in if inclProvedThs 
             then (head afterThis,
                   foldl (\lp provedGoal -> 
                     insertSentence lp (provedGoal{AS_Anno.isAxiom = True})) 
                         iLP 
                         (reverse proved))
             else (maybe (error ("SPASS.Prove.prepareLP: Goal "++goal++
                                 " not found!!"))
                         id (find ((==goal) . AS_Anno.senName) (goalsList s)),
                   iLP)
    getCfgText mp = ("{":lc, "{":lr)
      where
      (lc, lr) = 
        Map.foldWithKey (\ k cfg (lCfg,lRes) ->
                           let r = proof_status cfg
                               outp = resultOutput cfg
                           in
                           ((show k
                             ++ ":=GenericConfig {"
                             ++ "timeLimit = " ++ show (timeLimit cfg)
                             ++ ", timeLimitExceeded = "
                             ++ show (timeLimitExceeded cfg)
                             ++ ", extraOpts = "
                             ++ show (extraOpts cfg)
                             ++ "}," ):lCfg,
                            (show k
                             ++ ":=\n    ("
                             ++ show r ++ ",\n     \""
                             ++ (unlines outp) ++ "\")"):lRes))
                        (["}"],["}"]) mp
    transNames nm pStat = 
        pStat { goalName = trN $ goalName pStat
              , usedAxioms = foldr (fil $ trN $ goalName pStat) [] $ 
                             usedAxioms pStat }
        where trN x' = Map.findWithDefault 
                        (error ("Lookup of name failed: (2) "++
                                "should not happen \""++x'++"\""))
                        x' nm
              fil g ax axs = 
                  maybe (trace ("*** SPASS Warning: unknown axiom \""++
                                ax++"\" omitted from list of used\n"++
                                "      axioms of goal \""++g++"\"")
                                  axs) (:axs) (Map.lookup ax nm)

-- * Non-interactive Batch Prover

-- ** Constants

{- |
  Time limit used by the batch mode prover.
-}
batchTimeLimit :: Int
batchTimeLimit = 20

-- ** Utility Functions

{- |
  reads ENV-variable HETS_SPASS_BATCH_TIME_LIMIT and if it exists and has an Int-value this value is returned otherwise the value of 'batchTimeLimit' is returned.
-}

getBatchTimeLimit :: IO Int
getBatchTimeLimit = do
   is <- Exception.catch (getEnv "HETS_SPASS_BATCH_TIME_LIMIT")
               (\e -> case e of 
                      Exception.IOException ie -> 
                          if isDoesNotExistError ie -- == NoSuchThing
                          then return $ show batchTimeLimit
                          else Exception.throwIO e
                      _ -> Exception.throwIO e)
   return (either (const batchTimeLimit) id (readEither is))

{- |
  Checks whether a goal in the results map is marked as proved.
-}
checkGoal :: SPASSConfigsMap -> SPIdentifier -> Bool
checkGoal cfgMap goal =
  isJust g && isProvedStat (proof_status $ fromJust g)
  where
    g = Map.lookup goal cfgMap

-- ** Implementation

{- |
  A non-GUI batch mode prover. Uses default configuration for SPASS.
  The list of goals is processed sequentially. Proved goals are inserted
  as axioms.
-}
spassProveBatch :: Int -- ^ batch time limit
                -> String -- ^ extra options passed
                -> Bool -- ^ True means include proved theorems
                -> (Int 
                    -> AS_Anno.Named SPTerm 
                    -> (SpassProverRetval, SPASSConfig) 
                    -> IO Bool) 
                    -- ^ called after every prover run. 
                    -- return True if you want the prover to continue.
                -> String -- ^ theory name
                -> SPASS.Prove.State
                -> IO ([Proof_status ()]) -- ^ proof status for each goal
spassProveBatch tLimit extraOptions inclProvedThs f thName st =
    batchProve (initialLogicalPart st) 0 [] (goalsList st)
  {- do -- putStrLn $ showPretty initialLogicalPart ""
     -- read batchTimeLimit from ENV variable if set otherwise use constant
     pstl <- {- trace (showPretty initialLogicalPart (show goals)) -} 
             batchProve (initialLogicalPart st) [] (goalsList st)
     -- putStrLn ("Outcome of proofs:\n" ++ unlines (map show pstl) ++ "\n")
     return pstl -}
  where
    openGoals = filterOpenGoals (configsMap st)

    addToLP g res lp = 
        if isProvedStat res && inclProvedThs
        then insertSentence lp (g{AS_Anno.isAxiom = True})
        else lp
    batchProve _ _ resDone [] = return (reverse resDone)
    batchProve lp goalsProcessedSoFar resDone (g:gs) = 
     let gName = AS_Anno.senName g
     in 
      if Map.member gName openGoals 
      then do
        putStrLn $ "Trying to prove goal: " ++ gName
        -- putStrLn $ show g
        (err, res_cfg) <- 
              runSpass lp ((emptyConfig gName) { timeLimit = Just tLimit
                                               , extraOpts = words extraOptions }) 
                       thName g
        let res = proof_status res_cfg
        putStrLn $ "SPASS returned: " ++ (show err)
        -- if the batch prover runs in a separate thread 
        -- that's killed via killThread
        -- runSpass will return SpassError. we have to stop the 
        -- recursion in that case
        case err of
          SpassError _ -> return ((reverse (res:resDone)) ++ 
                                  (map (openSPASSProof_status . 
                                         AS_Anno.senName) gs))
          _ -> do
               -- add proved goals as axioms
              let lp' = addToLP g res lp
                  goalsProcessedSoFar' = goalsProcessedSoFar+1
              cont <- f goalsProcessedSoFar' g (err, res_cfg)
              if cont
                 then batchProve lp' goalsProcessedSoFar' (res:resDone) gs
                 else return ((reverse (res:resDone)) ++ 
                              (map (openSPASSProof_status .
                                             AS_Anno.senName) gs))
      else batchProve (addToLP g (proof_status $ 
                                  Map.findWithDefault (emptyConfig gName)
                                     gName $ configsMap st)
                               lp)
                      goalsProcessedSoFar resDone gs
                                  

-- * SPASS Interfacing Code

{- |
  Reads and parses the output of SPASS.
-}
parseSpassOutput :: ChildProcess -- ^ the SPASS process
                 -> IO (Maybe String, [String], [String]) -- ^ (result, used axioms, complete output)
parseSpassOutput spass = parseProtected (parseStart True) (Nothing, [], [])
  where

    -- check for errors. unfortunately we cannot just read from SPASS until an
    -- EOF since readMsg will just wait forever on EOF.
    parseProtected f (res, usedAxs, output) = do
      e <- getToolStatus spass
      case e of
        Nothing
          -- still running
          -> f (res, usedAxs, output)
        Just (ExitFailure retval)
          -- returned error
          -> do
              _ <- waitForChildProcess spass
              return (Nothing, [], ["SPASS returned error: "++(show retval)])
        Just ExitSuccess
          -- completed successfully. read remaining output.
          -> f (res, usedAxs, output)

    -- the first line of SPASS output it always empty.
    -- the second contains SPASS-START in the usual case
    -- and an error message in case of an error
    parseStart firstline (res, usedAxs, output) = do
      line <- readMsg spass
      if firstline
        -- ignore empty first line
        then parseProtected (parseStart False) (res, usedAxs, output ++ [""])
        -- check for a potential error
        else do
          let startMatch = matchRegex re_start line
          if isJust startMatch
            -- got SPASS-START. continue parsing
            then parseProtected parseIt (res, usedAxs, output ++ [line])
            -- error. abort parsing
            else do
              e <- waitForChildProcess spass
              case e of
                ChildTerminated ->
                  return (Nothing, [], output ++ [line, "", "SPASS has been terminated."])
                ChildExited retval ->
                  return (Nothing, [], output ++ [line, "", "SPASS returned error: "++(show retval)])
          
    -- actual parsing. tries to read from SPASS until ".*SPASS-STOP.*" matches.
    parseIt (res, usedAxs, output) = do
      line <- readMsg spass
      let resMatch = matchRegex re_sb line
      let res' = if isJust resMatch then (Just $ head $ fromJust resMatch) else res
      let usedAxsMatch = matchRegex re_ua line
      let usedAxs' = if isJust usedAxsMatch then (words $ head $ fromJust usedAxsMatch) else usedAxs
      if seq (length line) $ isJust (matchRegex re_stop line)
        then do
          _ <- waitForChildProcess spass
          return (res', usedAxs', output ++ [line])
        else
          parseProtected parseIt (res', usedAxs', output ++ [line])

    -- regular expressions used for parsing
    re_start = mkRegex ".*SPASS-START.*"
    re_stop = mkRegex ".*SPASS-STOP.*"
    re_sb = mkRegex "SPASS beiseite: (.*)$"
    re_ua = mkRegex "Formulae used in the proof.*:(.*)$"

{- |
  Runs SPASS. SPASS is assumed to reside in PATH.
-}
runSpass :: SPLogicalPart -- ^ logical part containing the input Sign and axioms and possibly goals that have been proved earlier as additional axioms
         -> SPASSConfig -- ^ configuration to use
         -> String -- ^ name of the theory in the DevGraph
         -> AS_Anno.Named SPTerm -- ^ goal to prove
         -> IO (SpassProverRetval, SPASSConfig) -- ^ (retval, configuration with proof status and complete output)
runSpass lp cfg thName nGoal = do
  putStrLn ("running 'SPASS" ++ (concatMap (' ':) allOptions) ++ "'")
  spass <- newChildProcess "SPASS" [ChildProcess.arguments allOptions]
  Exception.catch (runSpassReal spass)
    (\ excep -> do
      -- kill spass process
      destroy spass
      _ <- waitForChildProcess spass
      return (case excep of
                -- this is supposed to distinguish "fd ... vanished" 
                -- errors from other exceptions
                Exception.IOException e -> 
                    (SpassError ("Internal error communicating "++
                                 "with SPASS.\n"++show e),
                                emptyConfig $ AS_Anno.senName nGoal)
                _ -> (SpassError ("Error running SPASS.\n"++show excep), 
                        emptyConfig $ AS_Anno.senName nGoal)
             ))

  where
    runSpassReal spass = do
      -- check if SPASS is running
      e <- getToolStatus spass
      if isJust e
        then return 
                 (SpassError "Could not start SPASS. Is SPASS in your $PATH?", 
                  emptyConfig $ AS_Anno.senName nGoal)
        else do
          prob <- genSPASSProblem thName lp (Just nGoal)
          sendMsg spass (showPretty prob "")
          (res, usedAxs, output) <- parseSpassOutput spass
          let (err, retval) = proof_status res usedAxs cleanOptions
          return (err,
                  cfg{proof_status = retval,
                      resultOutput = output})

    filterOptions = ["-DocProof", "-Stdin", "-TimeLimit"]
    cleanOptions = filter (\ opt -> not (or (map (flip isPrefixOf opt) 
                                                 filterOptions))) 
                          (extraOpts cfg)
    tLimit = if isJust (timeLimit cfg)
               then fromJust (timeLimit cfg)
               -- this is OK. the batch prover always has the time limit set
               else guiDefaultTimeLimit
    allOptions = cleanOptions ++ ["-DocProof", "-Stdin", "-TimeLimit=" ++ (show tLimit)]
    defaultProof_status opts = 
        (openSPASSProof_status (AS_Anno.senName nGoal))
        {tacticScript = Tactic_script $ concatMap (' ':) opts}

    proof_status res usedAxs options
      | isJust res && elem (fromJust res) proved =
          (SpassSuccess,
           (defaultProof_status options)
           { goalStatus = Proved $ if elem (AS_Anno.senName nGoal) usedAxs
                                   then Nothing
                                   else Just False
           , usedAxioms = filter (/=(AS_Anno.senName nGoal)) usedAxs })
      | isJust res && elem (fromJust res) disproved =
          (SpassSuccess,  
           (defaultProof_status options) { goalStatus = Disproved } )
      | isJust res && elem (fromJust res) timelimit =
          (SpassTLimitExceeded, defaultProof_status options)
      | isNothing res =
          (SpassError "Internal error.", defaultProof_status options)
      | otherwise = (SpassSuccess, defaultProof_status options)
    proved = ["Proof found."]
    disproved = ["Completion found."]
    timelimit = ["Ran out of time."]

