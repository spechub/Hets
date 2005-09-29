{- |
Module      :  $Header$
Description :  Interface for the SPASS theorem prover.
Copyright   :  (c) Rene Wagner, Klaus Lüttich, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rwagner@tzi.de
Stability   :  provisional
Portability :  needs POSIX

Interface for the SPASS theorem prover.
See <http://spass.mpi-sb.mpg.de/> for details on SPASS.

-}

{- 
    todo:
      - use one of the technices in Comorphisms.CASL2SPASS to translate
        formula labels into correct SPASS identifiers; 
        and keep track of this translation for getting the right names
        for ProofStatus ...
        partly implemented
      - Implement a consistency checker based on GUI
      - check if proving is possible more than one time even 
        if the Goal was already proved
-}

module SPASS.Prove where

import Control.Exception

import Logic.Prover

import SPASS.Sign
import SPASS.Conversions
import SPASS.ProveHelp
import SPASS.Translate

import Common.AS_Annotation
import Common.PrettyPrint
import Common.ProofUtils

import ChildProcess
import ProcessClasses
import System.Exit
import Text.Regex
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
data SPASSConfig = SPASSConfig { -- | time limit in seconds passed to SPASS via -TimeLimit. Default will be used if Nothing.
                                 timeLimit :: Maybe Int,
                                 -- | True if timelimit exceed during last prover run
                                 timeLimitExceeded :: Bool,
                                 -- | extra options passed verbatimely to SPASS. -DocProof, -Stdin, and -TimeLimit will be overridden.
                                 extraOpts :: [String]
                               } deriving (Eq, Ord, Show)

{- |
  Creates an empty SPASSConfig. Default time limit and no extra options.
-}
emptyConfig :: SPASSConfig
emptyConfig = SPASSConfig {timeLimit = Nothing,
                           timeLimitExceeded = False,
                           extraOpts = []}

{- |
  Utility function to set the time limit of a SPASSConfig.
  For values <= 0 a default value is used.
-}
setTimeLimit :: Int -> SPASSConfig -> SPASSConfig
setTimeLimit n c = if n > 0 then c{timeLimit = Just n} else c{timeLimit = Nothing}

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

{- |
  Represents the result of a prover run.
  (Proof_status, full output)
-}
type SPASSResult = (Proof_status (), [String])


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
  Creates an empty SPASSConfigsMap.
-}
emptyConfigsMap :: SPASSConfigsMap
emptyConfigsMap = Map.empty

{- |
  Adjusts the configuration associated to a goal by applying the supplied
  function or inserts a new emptyConfig with the function applied if there's
  no configuration associated yet.

  Uses Map.member, Map.adjust, and Map.insert for the corresponding tasks
  internally.
-}
adjustOrSetConfig :: (SPASSConfig -> SPASSConfig) -- ^ function to be applied against the current configuration or a new emptyConfig
                  -> SPIdentifier -- ^ name of the goal
                  -> SPASSConfigsMap -- ^ current SPASSConfigsMap
                  -> SPASSConfigsMap -- ^ resulting SPASSConfigsMap with the changes applied
adjustOrSetConfig f k m = if (Map.member k m)
                            then Map.adjust f k m
                            else Map.insert k (f emptyConfig) m

{- |
  Performs a lookup on the ConfigsMap. Returns the config for the goal or an
  empty config if none is set yet.
-}
getConfig :: SPIdentifier -> SPASSConfigsMap -> SPASSConfig
getConfig spid m = if (isJust lookupId)
                     then fromJust lookupId
                     else emptyConfig
  where
    lookupId = Map.lookup spid m

{- |
  Store one result per goal.
-}
type SPASSResultsMap = Map.Map SPIdentifier SPASSResult

{- |
  Creates an empty SPASSResultsMap.
-}
emptyResultsMap :: SPASSResultsMap
emptyResultsMap = Map.empty

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
                     theory :: Theory Sign Sentence,
                     -- | stores the prover configurations for each goal
                     configsMap :: SPASSConfigsMap,
                     -- | stores the results retrieved by running SPASS for each goal
                     resultsMap :: SPASSResultsMap,
                     -- | stores a mapping to SPASS compliant identifiers for all goals
                     goalNamesMap :: SPASSGoalNameMap,
                     -- | list of all goals
                     goalsList :: [Named SPTerm]
                   }

{- |
  Creates an initial State around a Theory.
-}
initialState :: Theory Sign Sentence -> SPASSGoalNameMap 
             -> [Named Sentence] -> SPASS.Prove.State
initialState th gm gs = 
    State {currentGoal = Nothing,
           theory = th,
           configsMap = Map.fromList (map (\ g -> (senName g, emptyConfig) ) gs),
           resultsMap = emptyResultsMap,
           goalNamesMap = gm,
           goalsList = gs}

{- |
  Helper function to check if a goal has been proved.
-}
isProved :: (Proof_status a) -> Bool
isProved (Proved _ _ _ _ _) = True
isProved _ = False

-- ** Defining the view

{- |
  Colors used by the GUI to indicate the status of a goal.
-}
data ProofStatusColour
  -- | Proved
  = Green
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
toGuiStatus cf st = case st of
  Proved _ _ _ _ _ -> statusProved
  Disproved _ -> statusDisproved
  _ -> if timeLimitExceeded cf
         then statusOpenTExceeded
         else statusOpen

{- |
  Short 'String' representing a 'Proved' proof status in the 'ListBox' of
  the prover GUI.
-}
indicatorProved :: String
indicatorProved = "[+]"

{- |
  Short 'String' representing a 'Disproved' proof status in the 'ListBox' of
  the prover GUI.
-}
indicatorDisproved :: String
indicatorDisproved = "[-]"

{- |
  Short 'String' representing an 'Open' proof status in the 'ListBox' of
  the prover GUI.
-}
indicatorOpen :: String
indicatorOpen = "[ ]"

{- |
  Converts a 'Proof_status' into a short 'String' to be displayed by the GUI
  in a 'ListBox'.
-}
toStatusIndicator :: SPASSConfig -- ^ current prover configuration
                  -> (Proof_status a) -- ^ status to convert
                  -> String
toStatusIndicator _ st = case st of
  Proved _ _ _ _ _ -> indicatorProved
  Disproved _ -> indicatorDisproved
  _ -> indicatorOpen

{- |
  Generates a list of textual representations of all goals from a 
  'SPASS.Prove.State'.

  The resulting strings contain the result of 'toStatusIndicator'
  concatenated with the goal name.
-}
goalsView :: SPASS.Prove.State  -- ^ current global prover state
          -> [String] -- ^ resulting ['String'] list
goalsView s = map (\ g ->
                       let res = Map.lookup g (resultsMap s)
                           cf = Map.findWithDefault
                                (error "updateDisplay: configsMap \
                                       \was not initialised!!")
                                g (configsMap s)
                           statind = maybe indicatorOpen
                                       ((toStatusIndicator cf) . fst)
                                       res
                        in
                          statind ++ (' ':g))(map senName (goalsList s))

-- ** GUI Implementation

-- *** Utility Functions

{- |
  Retrieves the value of the time limit 'Entry'. Ignores invalid input.
-}
getValueSafe :: Entry Int -- ^ time limit 'Entry'
             -> IO Int -- ^ user-requested time limit or default in case of a parse error
getValueSafe timeEntry =
    catchJust userErrors ((getValue timeEntry) :: IO Int) 
                  (\ s -> trace ("Warning: Error "++show s++" was ignored") (return guiDefaultTimeLimit))
--    where selExcep ex = case ex of
--                        ErrorCall s 
--                            | isPrefixOf "NO PARSE:" s -> Just guiDefaultTimeLimit
--                        IOException x -> trace ("ICH:" ++ show x) Nothing
--                        _ -> Nothing

-- *** Callbacks

{- |
  Text displayed by the batch mode window.
-}
batchInfoText :: Int -- ^ total number of goals
              -> Int -- ^ number of that have been processed
              -> String
batchInfoText gTotal gDone =
  "Running prover in batch mode:\n"
  ++ show gDone ++ "/" ++ show gTotal ++ " goals processed.\n"
  ++ "At most " ++ (show ((gTotal - gDone) * batchTimeLimit)) ++ " seconds remaining."

{- |
  Called every time a goal has been processed in the batch mode gui.
-}
goalProcessed :: IORef SPASS.Prove.State -- ^ IORef pointing to the backing State data structure
              -> Int -- ^ total number of goals
              -> Label -- ^ info label
              -> Button -- ^ cancel (continue) button
              -> Named SPTerm -- ^ goal that has just been processed
              -> (SpassProverRetval, SPASSResult)
              -> IO Bool
goalProcessed stateRef numGoals label cbutton nGoal (retval, res) = do
  s <- readIORef stateRef

  let s' = s{resultsMap = Map.insert (senName nGoal) res (resultsMap s),
             configsMap = adjustOrSetConfig (\ c -> c{timeLimitExceeded = isTimeLimitExceeded retval}) (senName nGoal) (configsMap s)}
  writeIORef stateRef s'

  if (numGoals - (Map.size $ resultsMap s')) > 0
    then label # text (batchInfoText numGoals (Map.size $ resultsMap s'))
    else do
      cbutton # text "Continue"
      label # text "Batch mode finished. Click 'Continue' to see the results."

  -- always continue
  return True

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
    if updateLb
      then do
        selectedOld <- (getSelection goalsLb) :: IO (Maybe [Int])
        -- putStrLn $ show selectedOld
        goalsLb # value (goalsView st)
        -- putStrLn $ "activating: " ++ (show $ (head . fromJust) selectedOld)
        -- FIXME: while extracting this ListBox functionality, make sure 
        -- to activate multiple lines if it is allowed.
        when (isJust selectedOld) 
             (do selection (head (fromJust selectedOld)) goalsLb
                 return ())
      else return ()
    maybe (return ())
          (\ go -> 
               let mprfst = Map.lookup go (resultsMap st)
                   cf = Map.findWithDefault 
                        (error "updateDisplay: configsMap \
                               \was not initialised!!") 
                        go (configsMap st)
                   t' = maybe guiDefaultTimeLimit id (timeLimit cf)
                   opts' = unwords (extraOpts cf)
                   (color, label) = maybe statusOpen
                                    ((toGuiStatus cf) . fst)
                                    mprfst
                   usedAxioms = maybe []
                                (\s -> case (fst s) of
                                          Proved _ xs _ _ _ -> xs
                                          _ -> [])
                                mprfst

               in do 
                statusLabel # text label
                statusLabel # foreground (show color)
                timeEntry # value t'
                optionsEntry # value opts'
                axiomsLb # value (usedAxioms::[String])
                return ()) 
          (currentGoal st)

-- *** Main GUI

{- |
  Invokes the prover GUI. First runs the batch prover on all goals,
  then drops the user into a detailed GUI.
-}
spassProveGUI :: String -- ^ theory name
              -> Theory Sign Sentence -- ^ theory consisting of a SPASS.Sign.Sign and a list of Named SPASS.Sign.Sentence
              -> IO([Proof_status ()]) -- ^ proof status for each goal
spassProveGUI thName th = do
  -- backing data structure
  let initState = initialState th 
                  (collectNameMapping goals (filter isAxiom nSens)) goals
  stateRef <- newIORef initState

  -- batch window
  batchWin <- createToplevel [text $ thName ++ " - SPASS Prover"]
  pack batchWin [Expand On, Fill Both]

  batchB <- newVBox batchWin []
  pack batchB [Expand On, Fill Both]

  let numGoals = length goals

  batchL <- newLabel batchB [text $ batchInfoText numGoals 0]
  pack batchL []

  batchSp1 <- newSpace batchB (cm 0.15) []
  pack batchSp1 [Expand Off, Fill X, Side AtBottom]

  newHSeparator batchB

  batchSp2 <- newSpace batchB (cm 0.15) []
  pack batchSp2 [Expand Off, Fill X, Side AtBottom]

  batchCancelButton <- newButton batchB [text "Cancel Batch Mode"]
  pack batchCancelButton [Expand Off, Side AtRight]

  -- batch window events
  batchCancel <- clicked batchCancelButton

  batchProver <- Concurrent.forkIO (do
                                      _ <- spassProveBatch (goalProcessed stateRef numGoals batchL batchCancelButton) thName th
                                      return ())
  sync (batchCancel >>> do
                          -- putStrLn "killing batch prover"
                          Concurrent.killThread batchProver
                          destroy batchWin)

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

  s0 <- readIORef stateRef
  lb <- newListBox lbFrame [value $ goalsView s0, bg "white",
                            selectMode Single, height 15] :: IO (ListBox String)
  pack lb [Expand On, Side AtLeft, Fill Both]
  sb <- newScrollBar lbFrame []
  pack sb [Expand On, Side AtRight, Fill Y]
  lb # scrollbar Vertical sb

  -- right frame (options/results)
  right <- newFrame b2 []
  pack right [Expand On, Fill Both, Anchor NorthWest]

  spacer <- newLabel right [text "   "]
  grid spacer [GridPos (0,1), Sticky W, Sticky W]
  l1 <- newLabel right [text "Options:"]
  grid l1 [GridPos (0,0), Columnspan 2, Sticky W]
  l2 <- newLabel right [text "TimeLimit"]
  grid l2 [GridPos (1,1), Sticky W]
  (timeEntry :: Entry Int) <- newEntry right [width 18, value guiDefaultTimeLimit]
  grid timeEntry [GridPos (3,1), Sticky W]
  timeSpinner <- newSpinButton right (\sp -> synchronize main
                                     (do
                                        s <- readIORef stateRef
                                        if isJust (currentGoal s)
                                          then (do
                                            let goal = fromJust (currentGoal s)
                                            curEntTL <- getValueSafe timeEntry 
                                            let sEnt = s {configsMap = adjustOrSetConfig (setTimeLimit curEntTL) goal (configsMap s)}
                                            let cfg = getConfig goal (configsMap sEnt)
                                            let t = timeLimit cfg
                                            let t' = (case sp of
                                                           Up -> if isJust t then (fromJust t) + 10 else guiDefaultTimeLimit + 10
                                                           _ -> if isJust t then (fromJust t) - 10 else guiDefaultTimeLimit - 10)
                                            let s' = sEnt {configsMap = adjustOrSetConfig (setTimeLimit t') goal (configsMap sEnt)}
                                            writeIORef stateRef s'
                                            timeEntry # value (maybe guiDefaultTimeLimit id (timeLimit (getConfig goal (configsMap s'))))
                                            done)
                                          else noGoalSelected)) []
  grid timeSpinner [GridPos (3,1), Sticky E]
  l3 <- newLabel right [text "Extra Options:"]
  grid l3 [GridPos (1,2), Sticky W]
  (optionsEntry :: Entry String) <- newEntry right [width 37]
  grid optionsEntry [GridPos (1,3), Columnspan 3, Sticky W]
  proveButton <- newButton right [text "Prove"]
  grid proveButton [GridPos (2,4), Columnspan 2, Sticky E]
  l4 <- newLabel right [text "Results:"]
  grid l4 [GridPos (0,5), Columnspan 2, Sticky W]
  l5 <- newLabel right [text "Status"]
  grid l5 [GridPos (1,6), Sticky W]
  statusLabel <- newLabel right [text "Open"]
  grid statusLabel [GridPos (2,6), Columnspan 2, Sticky W]
  l6 <- newLabel right [text "Used Axioms"]
  grid l6 [GridPos (1,7), Sticky NW]
  axiomsFrame <- newFrame right []
  grid axiomsFrame [GridPos (2,7), Columnspan 2]
  axiomsLb <- newListBox axiomsFrame [value $ ([]::[String]), bg "white",
                                      selectMode Browse, height 6, width 20] :: IO (ListBox String)
  pack axiomsLb [Side AtLeft, Fill Y]
  axiomsSb <- newScrollBar axiomsFrame []
  pack axiomsSb [Side AtRight, Fill Y]
  axiomsLb # scrollbar Vertical axiomsSb
  detailsButton <- newButton right [text "Show Details"]
  grid detailsButton [GridPos (2,8), Columnspan 2, Sticky E]

  -- separator
  sp1 <- newSpace b (cm 0.15) []
  pack sp1 [Expand Off, Fill X, Side AtBottom]

  newHSeparator b

  sp2 <- newSpace b (cm 0.15) []
  pack sp2 [Expand Off, Fill X, Side AtBottom]

  -- bottom frame (help/save/exit buttons)
  bottom <- newFrame b []
  pack bottom [Expand Off, Fill Both]
  
  helpButton <- newButton bottom [text "Help"]
  grid helpButton [GridPos (0,0)]
  saveButton <- newButton bottom [text "Save Prover Configuration"]
  grid saveButton [GridPos (1,0)]
  exitButton <- newButton bottom [text "Exit Prover"]
  grid exitButton [GridPos (2,0)]

  -- events
  (selectGoal, _) <- bindSimple lb (ButtonPress (Just 1))
  doProve <- clicked proveButton
  showDetails <- clicked detailsButton
  help <- clicked helpButton
  saveConfiguration <- clicked saveButton
  exit <- clicked exitButton

  -- event handlers
  spawnEvent 
    (forever
      ((selectGoal >>> do
          s <- readIORef stateRef
          let oldGoal = currentGoal s
          curEntTL <- (getValueSafe timeEntry) :: IO Int
          let s' = if isJust oldGoal
                     then s {configsMap = adjustOrSetConfig
                                          (setTimeLimit curEntTL) (fromJust oldGoal) (configsMap s)}
                     else s
          sel <- (getSelection lb) :: IO (Maybe [Int])
          let s'' = if isJust sel
                      then s' {currentGoal = Just $ senName 
                                            (goals !! (head $ fromJust sel))}
                      else s'
          writeIORef stateRef s''
          updateDisplay s'' False lb statusLabel timeEntry optionsEntry axiomsLb
          done)
      +> (doProve >>> do
            rs <- readIORef stateRef
            if isNothing $ currentGoal rs
              then noGoalSelected
              else (do
                curEntTL <- (getValueSafe timeEntry) :: IO Int
                let goal = fromJust $ currentGoal rs
                let s = rs {configsMap = adjustOrSetConfig (setTimeLimit curEntTL) goal (configsMap rs)}
                let (beforeThis, afterThis) = splitAt (fromJust $ findIndex (\sen -> senName sen == goal) goals) goals
                let proved = filter (\sen-> checkGoal (resultsMap s) (senName sen)) beforeThis
                let lp' = foldl (\lp provedGoal -> insertSentence lp (provedGoal{isAxiom = True})) initialLogicalPart (reverse proved)
                extraOptions <- (getValue optionsEntry) :: IO String
                let s' = s {configsMap = adjustOrSetConfig (setExtraOpts (words extraOptions)) goal (configsMap s)}
                statusLabel # text (snd statusRunning)
                statusLabel # foreground (show $ fst statusRunning)
                (retval, (res, output)) <- runSpass lp' (getConfig goal (configsMap s')) (head afterThis)
                case retval of
                  SpassError message -> createErrorWin message []
                  _ -> return ()
                let s'' = s'{resultsMap = Map.insert goal (res, output) (resultsMap s'),
                             configsMap = adjustOrSetConfig (\ c -> c{timeLimitExceeded = isTimeLimitExceeded retval}) goal (configsMap s')}
                writeIORef stateRef s''
                updateDisplay s'' True lb statusLabel timeEntry optionsEntry axiomsLb
                done)
            done)
      +> (showDetails >>> do
            s <- readIORef stateRef
            if isNothing $ currentGoal s
              then noGoalSelected
              else (do
                let goal = fromJust $ currentGoal s
                let result = Map.lookup goal (resultsMap s)
                let output = if isJust result
                               then snd (fromJust result)
                               else ["This goal hasn't been run through the prover yet."]
                let detailsText = concatMap ('\n':) output
                createTextSaveDisplay ("SPASS Output for Goal "++goal) (goal ++ ".spass") detailsText
                done)
            done)
      +> (help >>> do
            createTextDisplay "SPASS Help" spassHelpText [size (80, 30)]
            done)
      +> (saveConfiguration >>> do
            s <- readIORef stateRef
            let cfgText = concatMap ((++"\n")) ["Configuration:\n", show $ configsMap s, "\nResults:\n", showResMap (resultsMap s)]
            createTextSaveDisplay ("SPASS Configuration for Theory " ++ thName) (thName ++ ".spcf") cfgText
            done)
      ))
  sync (exit >>> destroy main)
  s <- readIORef stateRef
  let proof_stats = map (\g -> let res = Map.lookup g (resultsMap s) in if isJust res then fst $ fromJust res else Open g) (map senName goals)
  return proof_stats
  where
    noGoalSelected = createErrorWin "Please select a goal first." []
    Theory sign nSens = th
    (axioms, goals) = partition isAxiom 
                          (prepareSenNames transSenName nSens)
    initialLogicalPart = foldl insertSentence (signToSPLogicalPart sign) (reverse axioms)
    showResMap mp = 
        '{':(foldr  (\ (k,(r,outp)) resF -> 
                             shows k . 
                             (++) ":=\n    (" .  
                             shows r . (++) ",\n     \"" .
                             (++) (unlines outp) . (++) "\")\n" . resF) id 
                    (Map.toList mp)) "}" 

-- * Non-interactive Batch Prover

-- ** Constants

{- |
  Time limit used by the batch mode prover.
-}
batchTimeLimit :: Int
batchTimeLimit = 15

-- ** Utility Functions

{- |
  Checks whether a goal in the results map is marked as proved.
-}
checkGoal :: SPASSResultsMap -> SPIdentifier -> Bool
checkGoal resMap goal =
  isJust g && isProved (fst $ fromJust g)
  where
    g = Map.lookup goal resMap

-- ** Implementation

{- |
  A non-GUI batch mode prover. Uses default configuration for SPASS.
  The list of goals is processed sequentially. Proved goals are inserted
  as axioms.
-}
spassProveBatch :: (Named SPTerm -> (SpassProverRetval, SPASSResult) -> IO Bool) -- ^ called after every prover run. return True if you want the prover to continue.
                -> String -- ^ theory name
                -> Theory Sign Sentence -- ^ theory consisting of a SPASS.Sign.Sign and a list of Named SPASS.Sign.Sentence
                -> IO([Proof_status ()]) -- ^ proof status for each goal
spassProveBatch f _ (Theory sig nSens) =
  do -- putStrLn $ showPretty initialLogicalPart ""
     pstl <- {- trace (showPretty initialLogicalPart (show goals)) -} (batchProve initialLogicalPart [] goals)
     -- putStrLn ("Outcome of proofs:\n" ++ unlines (map show pstl) ++ "\n")
     return pstl
  where
    batchProve _ resDone [] = return (reverse resDone)
    batchProve lp resDone (g:gs) = do
        putStrLn $ "Trying to prove goal: " ++ (senName g)
        -- putStrLn $ show g
        (err, (res, full)) <- runSpass lp (emptyConfig {timeLimit = Just batchTimeLimit}) g
        putStrLn $ "SPASS returned: " ++ (show err)
        -- if the batch prover runs in a separate thread that's killed via killThread
        -- runSpass will return SpassError. we have to stop the recursion in that
        -- case
        case err of
          SpassError _ -> return ((reverse (res:resDone)) ++ (map (Open . senName) gs))
          _ -> do
                 -- add proved goals as axioms
                 let lp' = if (isProved res)
                             then (insertSentence lp (g{isAxiom = True}))
                             else lp
                 cont <- f g (err, (res, full))
                 if cont
                   then batchProve lp' (res:resDone) gs
                   else return ((reverse (res:resDone)) ++ (map (Open . senName) gs))
    (axioms, goals) = partition isAxiom 
                          (prepareSenNames transSenName nSens)
    initialLogicalPart = foldl insertSentence (signToSPLogicalPart sig) (reverse axioms)

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
    parseProtected f (res, usedAxioms, output) = do
      e <- getToolStatus spass
      case e of
        Nothing
          -- still running
          -> f (res, usedAxioms, output)
        Just (ExitFailure retval)
          -- returned error
          -> do
              _ <- waitForChildProcess spass
              return (Nothing, [], ["SPASS returned error: "++(show retval)])
        Just ExitSuccess
          -- completed successfully. read remaining output.
          -> f (res, usedAxioms, output)

    -- the first line of SPASS output it always empty.
    -- the second contains SPASS-START in the usual case
    -- and an error message in case of an error
    parseStart firstline (res, usedAxioms, output) = do
      line <- readMsg spass
      if firstline
        -- ignore empty first line
        then parseProtected (parseStart False) (res, usedAxioms, output ++ [""])
        -- check for a potential error
        else do
          let startMatch = matchRegex re_start line
          if isJust startMatch
            -- got SPASS-START. continue parsing
            then parseProtected parseIt (res, usedAxioms, output ++ [line])
            -- error. abort parsing
            else do
              e <- waitForChildProcess spass
              case e of
                ChildTerminated ->
                  return (Nothing, [], output ++ [line, "", "SPASS has been terminated."])
                ChildExited retval ->
                  return (Nothing, [], output ++ [line, "", "SPASS returned error: "++(show retval)])
          
    -- actual parsing. tries to read from SPASS until ".*SPASS-STOP.*" matches.
    parseIt (res, usedAxioms, output) = do
      line <- readMsg spass
      let resMatch = matchRegex re_sb line
      let res' = if isJust resMatch then (Just $ head $ fromJust resMatch) else res
      let usedAxiomsMatch = matchRegex re_ua line
      let usedAxioms' = if isJust usedAxiomsMatch then (words $ head $ fromJust usedAxiomsMatch) else usedAxioms
      if isJust (matchRegex re_stop line)
        then do
          _ <- waitForChildProcess spass
          return (res', usedAxioms', output ++ [line])
        else
          parseProtected parseIt (res', usedAxioms', output ++ [line])

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
         -> Named SPTerm -- ^ goal to prove
         -> IO (SpassProverRetval, SPASSResult) -- ^ (retval, (proof status, complete output))
runSpass lp cfg nGoal = do
  putStrLn ("running 'SPASS" ++ (concatMap (' ':) allOptions) ++ "'")
  spass <- newChildProcess "SPASS" [ChildProcess.arguments allOptions]
  Exception.catch (runSpassReal spass nGoal)
    (\ excep -> do
      -- kill spass process
      destroy spass
      _ <- waitForChildProcess spass
      return (case excep of
                -- this is supposed to distinguish "fd ... vanished" errors from other exceptions
                IOException e -> (SpassError ("Internal error communicating with SPASS.\n"++show e),
                                    (Open (senName nGoal), []))
                _ -> (SpassError ("Error running SPASS.\n"++show excep), 
                        (Open (senName nGoal), []))))

  where
    runSpassReal spass namedGoal = do
      -- check if SPASS is running
      e <- getToolStatus spass
      if isJust e
        then return (SpassError "Could not start SPASS. Is SPASS in your $PATH?", (Open (senName namedGoal), []))
        else do
          -- debugging output
          -- putStrLn ("This will be sent to SPASS:\n" ++ showPretty problem "\n")
          -- FIXME: use printText0 instead. but where to get an instance of
          -- GlobalAnnos from?
          -- This can't be fixed until the prover interface is updated to hand
          -- in global annos
          sendMsg spass (showPretty problem "")
          (res, usedAxioms, output) <- parseSpassOutput spass
          let (err, retval) = proof_status res usedAxioms cleanOptions
          return (err, (retval, output))

    -- FIXME: this should be retrieved from the user instead of being hardcoded.
    problem = SPProblem {identifier = "hets_exported",
                         description = SPDescription {name = "hets_exported",
                                                      author = "hets user",
                                                      SPASS.Sign.version = Nothing,
                                                      logic = Nothing,
                                                      status = SPStateUnknown,
                                                      desc = "",
                                                      date = Nothing},
                         logicalPart = insertSentence lp nGoal}
    filterOptions = ["-DocProof", "-Stdin", "-TimeLimit"]
    cleanOptions = filter (\ opt -> not (or (map (flip isPrefixOf opt) filterOptions))) (extraOpts cfg)
    tLimit = if isJust (timeLimit cfg)
               then fromJust (timeLimit cfg)
               -- this is OK. the batch prover always has the time limit set
               else guiDefaultTimeLimit
    allOptions = cleanOptions ++ ["-DocProof", "-Stdin", "-TimeLimit=" ++ (show tLimit)]

    proof_status res usedAxioms options
      | isJust res && elem (fromJust res) proved =
          (SpassSuccess, Proved (senName nGoal) usedAxioms "SPASS" () (Tactic_script (concatMap (' ':) options)))
      | isJust res && elem (fromJust res) disproved =
          (SpassSuccess, Disproved (senName nGoal))
      | isJust res && elem (fromJust res) timelimit =
          (SpassTLimitExceeded, Open (senName nGoal))
      | isNothing res =
          (SpassError "Internal error.", Open (senName nGoal))
      | otherwise = (SpassSuccess, Open (senName nGoal))
    proved = ["Proof found."]
    disproved = ["Completion found."]
    timelimit = ["Ran out of time."]
