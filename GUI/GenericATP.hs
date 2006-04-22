{- |
Module      :  $Header$
Description :  Generic Prover GUI.
Copyright   :  (c) Klaus Lüttich, Rainer Grabbe, Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rainer25@tzi.de
Stability   :  provisional
Portability :  needs POSIX

Generic GUI for theorem provers. Based upon former SPASS Prover GUI.

-}

{- ToDo:

   - ATPFunctions in genericATPgui richtig verwenden
   - state initialisieren
   - kleine GUI mit Exit-Button lauffaehig aufbauen
   
   - import graphical functions from old SPASS/Prove.hs
   - generalize graphical functions
   
-}

module GUI.GenericATP where

import Logic.Prover

import qualified Common.AS_Annotation as AS_Anno
-- import Common.ProofUtils
import Common.PrettyPrint 
import qualified Common.Lib.Map as Map
-- import qualified Common.OrderedMap as OMap

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
-- import Messages
-- import TextDisplay
-- import Separator
-- import XSelection
-- import Space

import GUI.HTkUtils

-- import Proofs.GUIState
-- import Logic.Logic
-- import Logic.Grothendieck
-- import qualified Comorphisms.KnownProvers as KnownProvers
-- import qualified Static.DevGraph as DevGraph

import GUI.GenericATPState

-- debugging
import Debug.Trace


-- * Data Structures and assorted utility functions

data ThreadState = TSt { batchId :: Maybe Concurrent.ThreadId
                       , batchStopped :: Bool
                       }

initialThreadState :: ThreadState
initialThreadState = TSt { batchId = Nothing
                         , batchStopped = False}

{- |
  Utility function to set the time limit of a Config.
  For values <= 0 a default value is used.
-}
setTimeLimit :: Int -> GenericConfig proof_tree -> GenericConfig proof_tree
setTimeLimit n c = if n > 0 then c{timeLimit = Just n} 
                   else c{timeLimit = Nothing}

{- |
  Utility function to set the extra options of a Config.
-}
setExtraOpts :: [String] -> GenericConfig proof_tree -> GenericConfig proof_tree
setExtraOpts opts c = c{extraOpts = opts}

{- |
  Checks whether an ATPRetval indicates that the time limit was
  exceeded.
-}
isTimeLimitExceeded :: ATPRetval -> Bool
isTimeLimitExceeded ATPTLimitExceeded = True
isTimeLimitExceeded _ = False


{- |
  Adjusts the configuration associated to a goal by applying the supplied
  function or inserts a new emptyConfig with the function applied if there's
  no configuration associated yet.

  Uses Map.member, Map.adjust, and Map.insert for the corresponding tasks
  internally.
-}
adjustOrSetConfig :: (Ord proof_tree) =>
                     (GenericConfig proof_tree -> GenericConfig proof_tree) 
                     -- ^ function to be applied against the current 
                     -- configuration or a new emptyConfig
                  -> String -- ^ name of the prover
                  -> ATPIdentifier -- ^ name of the goal
                  -> proof_tree
                  -> GenericConfigsMap proof_tree -- ^ current GenericConfigsMap
                  -> GenericConfigsMap proof_tree
                  -- ^ resulting GenericConfigsMap with the changes applied
adjustOrSetConfig f prName k pt m = if (Map.member k m)
                                    then Map.adjust f k m
                                    else Map.insert k
                                               (f $ emptyConfig prName k pt) m

{- |
  Performs a lookup on the ConfigsMap. Returns the config for the goal or an
  empty config if none is set yet.
-}
getConfig :: (Ord proof_tree) =>
             String -- ^ name of the prover
          -> ATPIdentifier -- ^ name of the goal
          -> proof_tree
          -> GenericConfigsMap proof_tree
          -> GenericConfig proof_tree
getConfig prName genid pt m = maybe (emptyConfig prName genid pt)
                                id lookupId
  where
    lookupId = Map.lookup genid m

filterOpenGoals :: GenericConfigsMap proof_tree -> GenericConfigsMap proof_tree
filterOpenGoals = Map.filter isOpenGoal 
    where isOpenGoal cf = case (goalStatus $ proof_status cf) of
                              Open -> True
                              _    -> False

-- ** Constants

{- |
  Default time limit for the GUI mode prover in seconds.
-}
guiDefaultTimeLimit :: Int
guiDefaultTimeLimit = 10


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
toGuiStatus :: GenericConfig proof_tree -- ^ current prover configuration
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

{- |
  Generates a list of 'GUI.HTkUtils.LBGoalView' representations of all goals
  from a 'GenericATPState.GenericState'.
-}
goalsView :: GenericState sign sentence proof_tree pst -- ^ current global prover state
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
goalProcessed :: (Ord proof_tree) =>
                 IORef (GUI.GenericATPState.GenericState
                         sign sentence proof_tree pst)
               -- ^ IORef pointing to the backing State data structure
              -> Int -- ^ batch time limit
              -- -> String -- ^ extra options
              -> Int -- ^ total number of goals
              -> Label -- ^ info label
              -> String -- ^ name of the prover
              -> Int -- ^ number of goals processed so far
              -> AS_Anno.Named sentence -- ^ goal that has just been processed
              -> (ATPRetval, GenericConfig proof_tree)
              -> IO Bool
goalProcessed stateRef tLimit numGoals label prName
              processedGoalsSoFar nGoal (retval, res_cfg) = do
  s <- readIORef stateRef
  let s' = s{
      configsMap = adjustOrSetConfig 
                      (\ c -> c{timeLimitExceeded = 
                                    isTimeLimitExceeded retval,
                                timeLimit = Just tLimit,
                                proof_status = proof_status res_cfg,
                                resultOutput = resultOutput res_cfg})
                      prName (AS_Anno.senName nGoal) 
                      (proof_tree s)
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
updateDisplay :: GUI.GenericATPState.GenericState sign sentence proof_tree pst
                 -- ^ current global prover state
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

-- !! rewrite haddock comment
{- |
  Invokes the prover GUI. First runs the batch prover on all goals,
  then drops the user into a detailed GUI.
-}


genericATPgui :: (Ord proof_tree, Ord sentence, Show sentence) =>
                 ATPFunctions sign sentence proof_tree pst -- ^ prover specific functions
              -> String -- ^ prover name
              -> String -- ^ theory name
              -> Theory sign sentence proof_tree -- ^ theory consisting of a signature and a list of Named sentence
              -> proof_tree
              -> IO([Proof_status proof_tree]) -- ^ proof status for each goal
genericATPgui atpFun prName thName th pt = do
  -- create initial backing data structure
  let initState = initialGenericState prName thName
                    (initialProverState atpFun)
                    (atpTransSenName atpFun) th pt
  stateRef <- newIORef initState
-- !! read ENV from ATPFunctions or pst
--  batchTLimit <- getBatchTimeLimit $ "HETS_SPASS_BATCH_TIME_LIMIT"

  -- main window
  main <- createToplevel [text $ thName ++ " - " ++ prName ++ " Prover"]
  pack main [Expand On, Fill Both]

-- !! just for having a running window
  exitButton <- newButton main [text "Exit Prover"]
  pack exitButton []

  putWinOnTop main

  -- IORef for batch thread
  threadStateRef <- newIORef initialThreadState

  -- events
  exit <- clicked exitButton

  (closeWindow,_) <- bindSimple main Destroy

  -- event handlers
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
                                  else openProof_status g' (prName) $
                                       proof_tree s) 
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
  reads passed ENV-variable and if it exists and has an Int-value this value is returned otherwise the value of 'batchTimeLimit' is returned.
-}

getBatchTimeLimit :: String -- ^ ENV-variable containing batch time limit
                  -> IO Int
getBatchTimeLimit env = do
   is <- Exception.catch (getEnv env)
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
checkGoal :: GenericConfigsMap proof_tree -> ATPIdentifier -> Bool
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

{-
genericProveBatch :: Int -- ^ batch time limit
                  -> String -- ^ extra options passed
                  -> Bool -- ^ True means include proved theorems
                  -> (Int 
                      -> AS_Anno.Named sentence
                      -> (ATPRetval, GenericConfig proof_tree)
                      -> IO Bool) 
                      -- ^ called after every prover run. 
                      -- return True if you want the prover to continue.
                  -> (pst -> AS_Anno.Named sentence -> pst)
                      -- ^ inserts a Namend sentence into a logicalPart
                  -> String -- ^ prover name
                  -> String -- ^ theory name
                  -> GenericState sign sentence proof_tree pst
                  -> IO ([Proof_status proof_tree]) -- ^ proof status for each goal
genericProveBatch tLimit extraOptions inclProvedThs f inSen
                  prName thName st =
    batchProve (initialLogicalPart $ proverState st) 0 [] (goalsList st)
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
        then inSen lp (g{AS_Anno.isAxiom = True})
        else lp
    batchProve _ _ resDone [] = return (reverse resDone)
    batchProve lp goalsProcessedSoFar resDone (g:gs) =
     let gName = AS_Anno.senName g
         pt    = proof_tree st
     in
      if Map.member gName openGoals
      then do
        putStrLn $ "Trying to prove goal: " ++ gName
        -- putStrLn $ show g
        (err, res_cfg) <-
              runProver lp ((emptyConfig prName gName pt)
                             { timeLimit = Just tLimit
                             , extraOpts = words extraOptions })
                        thName g
        let res = proof_status res_cfg
        putStrLn $ prName ++ " returned: " ++ (show err)
        -- if the batch prover runs in a separate thread
        -- that's killed via killThread
        -- runSpass will return GenericError. we have to stop the
        -- recursion in that case
        case err of
          ATPError _ -> return ((reverse (res:resDone)) ++ 
                                (map (\ gl -> openProof_status
                                                (AS_Anno.senName gl) prName pt)
                                     gs))
          _ -> do
               -- add proved goals as axioms
              let lp' = addToLP g res lp
                  goalsProcessedSoFar' = goalsProcessedSoFar+1
              cont <- f goalsProcessedSoFar' g (err, res_cfg)
              if cont
                 then batchProve lp' goalsProcessedSoFar' (res:resDone) gs
                 else return ((reverse (res:resDone)) ++ 
                                (map (\ gl -> openProof_status
                                                (AS_Anno.senName gl) prName pt)
                                     gs))
      else batchProve (addToLP g (proof_status $ 
                                  Map.findWithDefault (emptyConfig prName gName pt)
                                     gName $ configsMap st)
                               lp)
                      goalsProcessedSoFar resDone gs
-}
