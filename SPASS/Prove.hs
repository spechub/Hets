{- |
Module      :  $Header$
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
      - surround goal specific part of GUI with a border and Status part 
        with another border
      - check if proving is possible more than one time even 
        if the Goal was already proved
-}

module SPASS.Prove where

import Control.Exception

import Logic.Prover

import SPASS.Sign
import SPASS.Conversions
import SPASS.Print
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

import HTk
import SpinButton
import ModalDialog
import DialogWin
import TextDisplay
import Separator
import Space

import GUI.HTkUtils

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel

-- debugging
import Debug.Trace

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
  We need to store one SPASSConfig per goal.
-}
type SPASSConfigsMap = Map.Map SPIdentifier SPASSConfig

{- |
  Creates an empty SPASSConfigsMap.
-}
emptyConfigsMap :: SPASSConfigsMap
emptyConfigsMap = Map.empty

{- |
-}
adjustOrSetConfig :: (SPASSConfig -> SPASSConfig) -> SPIdentifier -> SPASSConfigsMap -> SPASSConfigsMap
adjustOrSetConfig f k m = if (Map.member k m)
                            then Map.adjust f k m
                            else Map.insert k (f emptyConfig) m

{- |
  Performs a lookup on the ConfigsMap. Returns the config for the goal or an
  empty config if none is set yet.
-}
getConfig :: SPIdentifier -> SPASSConfigsMap -> SPASSConfig
getConfig id m = if (isJust lookupId)
                   then fromJust lookupId
                   else emptyConfig
  where
    lookupId = Map.lookup id m

{- |
  Default time limit.
-}
defaultTimeLimit :: Int
defaultTimeLimit = 10

{- |
  Represents the result of a prover run.
  (Proof_status, full output)
-}
type SPASSResult = (Proof_status (), [String])

{- |
  Store one result per goal.
-}
type SPASSResultsMap = Map.Map SPIdentifier SPASSResult

{- |
  Creates an empty SPASSResultsMap.
-}
emptyResultsMap :: SPASSResultsMap
emptyResultsMap = Map.empty

type SPASSGoalNameMap = Map.Map String String

{- |
  Represents the global state of the prover GUI.
-}
data State = State { currentGoal :: Maybe SPIdentifier,
                     theory :: Theory Sign Sentence,
                     configsMap :: SPASSConfigsMap,
                     resultsMap :: SPASSResultsMap,
                     goalNamesMap :: SPASSGoalNameMap
                   }

{- |
  Creates an initial State around a Theory.
-}
initialState :: Theory Sign Sentence -> SPASSGoalNameMap 
             -> [Named Sentence] -> SPASS.Prove.State
initialState th gm gs = 
    State {currentGoal = Nothing,
           theory = th,
           configsMap = Map.fromList (map (\ x -> (senName x,emptyConfig) ) gs),
           resultsMap = emptyResultsMap,
           goalNamesMap = gm}

data SpassProverRetval = SpassSuccess
                       | SpassTLimitExceeded
		       | SpassError String
  deriving (Eq, Show)

isTimeLimitExceeded :: SpassProverRetval -> Bool
isTimeLimitExceeded SpassTLimitExceeded = True
isTimeLimitExceeded _ = False

{- |
  Currently implemented as a batch mode prover only.
-}
spassProver :: Prover Sign Sentence ()
spassProver =
  Prover { prover_name = "SPASS",
           prover_sublogic = "SPASS",
           prove = spassProveGUI
         }

{- |
  Helper function to check if a goal has been proved.
-}
isProved :: (Proof_status a) -> Bool
isProved (Proved _ _ _ _ _) = True
isProved _ = False

{- |
  Green: Proved, Red: Disproved, Black: Open, Blue: Running
-}
data ProofStatusColour = Green | Red | Black | Blue
   deriving (Bounded,Enum,Show)

statusProved, statusDisproved, statusOpen, statusRunning :: (ProofStatusColour, String)
statusProved        = (Green, "Proved")
statusDisproved     = (Red, "Disproved")
statusOpen          = (Black, "Open")
statusOpenTExceeded = (Black, "Open (Time is up!)")
statusRunning       = (Blue, "Running")


{- |
   updates the display of the status of the goal
-}

-- updateDisplay :: SPASS.Prove.State -> Entry Int 
--              -> Entry String
updateDisplay state statusLabel timeEntry optionsEntry axiomsLb =
    maybe (return ())
          (\ go -> 
               let mprfst = Map.lookup go (resultsMap state)
                   cf = Map.findWithDefault 
                        (error "updateDisplay: configsMap \
                               \was not initialised!!") 
                        go (configsMap state)
                   t' = maybe defaultTimeLimit id (timeLimit cf)
                   opts' = unwords (extraOpts cf)
                   toGuiStatus st = case st of
                                    Proved _ _ _ _ _ -> statusProved
                                    Disproved _ -> statusDisproved
                                    _ -> if timeLimitExceeded cf
				           then statusOpenTExceeded
					   else statusOpen
		   (color, label) = maybe statusOpen
		                    (toGuiStatus . fst)
				    mprfst
		   usedAxioms = maybe []
		                (\st -> case (fst st) of
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
          (currentGoal state)

getValueSave :: Entry Int -> IO Int
getValueSave timeEntry =
    catchJust userErrors ((getValue timeEntry) :: IO Int) 
                  (\ s -> trace ("Warning: Error "++show s++" was ignored") (return defaultTimeLimit))
    where selExcep ex = case ex of
                        ErrorCall s 
                            | isPrefixOf "NO PARSE:" s -> Just defaultTimeLimit
                        IOException x -> trace ("ICH:" ++ show x) Nothing
                        _ -> Nothing


{- |
  Invokes the prover GUI. Not yet fully implemented.
-}
spassProveGUI :: String -- ^ theory name
              -> Theory Sign Sentence -- ^ theory consisting of a SPASS.Sign.Sign and a list of Named SPASS.Sign.Sentence
              -> IO([Proof_status ()]) -- ^ proof status for each goal
spassProveGUI thName th = do
  -- backing data structure
  let initState = initialState th 
                  (collectNameMapping goals (filter isAxiom nSens)) goals
  stateRef <- newIORef initState

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

  lb <- newListBox lbFrame [value $ map senName goals, bg "white",
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
  (timeEntry :: Entry Int) <- newEntry right [width 18, value defaultTimeLimit]
  grid timeEntry [GridPos (3,1), Sticky W]
  timeSpinner <- newSpinButton right (\sp -> synchronize main
                                     (do
                                        s <- readIORef stateRef
                                        if isJust (currentGoal s)
                                          then (do
                                            let goal = fromJust (currentGoal s)
                                            curEntTL <- getValueSave timeEntry 
                                            let sEnt = s {configsMap = adjustOrSetConfig (setTimeLimit curEntTL) goal (configsMap s)}
                                            let config = getConfig goal (configsMap sEnt)
                                            let t = timeLimit config
                                            let t' = (case sp of
                                                           Up -> if isJust t then (fromJust t) + 10 else defaultTimeLimit + 10
                                                           _ -> if isJust t then (fromJust t) - 10 else defaultTimeLimit - 10)
                                            let s' = sEnt {configsMap = adjustOrSetConfig (setTimeLimit t') goal (configsMap sEnt)}
                                            writeIORef stateRef s'
                                            timeEntry # value (maybe defaultTimeLimit id (timeLimit (getConfig goal (configsMap s'))))
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
  prove <- clicked proveButton
  showDetails <- clicked detailsButton
  help <- clicked helpButton
  saveConfiguration <- clicked saveButton
  exit <- clicked exitButton

  -- event handlers
  spawnEvent 
    (forever
      ((selectGoal >>> do
          s <- readIORef stateRef
          sel <- (getSelection lb) :: IO (Maybe [Int])
          let s' = if isJust sel
                     then s {currentGoal = Just $ senName 
                                           (goals !! (head $ fromJust sel))}
                     else s
          writeIORef stateRef s'
          updateDisplay s' statusLabel timeEntry optionsEntry axiomsLb
          done)
      +> (prove >>> do
            rs <- readIORef stateRef
            if isNothing $ currentGoal rs
              then noGoalSelected
              else (do
                curEntTL <- (getValueSave timeEntry) :: IO Int
                let goal = fromJust $ currentGoal rs
                let s = rs {configsMap = adjustOrSetConfig (setTimeLimit curEntTL) goal (configsMap rs)}
                let (before, after)= splitAt (fromJust $ findIndex (\sen -> senName sen == goal) goals) goals
                let proved = filter (\sen-> checkGoal (resultsMap s) (senName sen)) before
                let lp' = foldl (\lp x -> insertSentence lp (x{isAxiom = True})) initialLogicalPart (reverse proved)
                extraOptions <- (getValue optionsEntry) :: IO String
                let s' = s {configsMap = adjustOrSetConfig (setExtraOpts (words extraOptions)) goal (configsMap s)}
		statusLabel # text (snd statusRunning)
		statusLabel # foreground (show $ fst statusRunning)
                (retval, (res, output)) <- runSpass lp' (getConfig goal (configsMap s')) (head after)
		case retval of
		  SpassError message -> createErrorWin message []
		  _ -> return ()
                let s'' = s'{resultsMap = Map.insert goal (res, output) (resultsMap s'),
		             configsMap = adjustOrSetConfig (\ c -> c{timeLimitExceeded = isTimeLimitExceeded retval}) goal (configsMap s')}
                writeIORef stateRef s''
                updateDisplay s'' statusLabel timeEntry optionsEntry axiomsLb
                done)
            done)
      +> (showDetails >>> do
            s <- readIORef stateRef
            if isNothing $ currentGoal s
              then noGoalSelected
              else (do
                let goal = fromJust $ currentGoal s
                let result = Map.lookup goal (resultsMap s)
                let output = if isJust result then snd (fromJust result) else ["This goal hasn't been run through the prover yet."]
                let text = concatMap ('\n':) output
                createTextSaveDisplay ("SPASS Output for Goal "++goal) (goal ++ ".spass") text
                done)
            done)
      +> (help >>> do
            createTextDisplay "SPASS Help" spassHelpText [size (80, 30)]
            done)
      +> (saveConfiguration >>> do
            s <- readIORef stateRef
            let text = concatMap ((++"\n")) ["Configuration:\n", show $ configsMap s, "\nResults:\n", showResMap (resultsMap s)]
            createTextSaveDisplay ("SPASS Configuration for Theory " ++ thName) (thName ++ ".spcf") text
            done)
      ))
  sync (exit >>> destroy main)
  s <- readIORef stateRef
  let proof_stats = map (\x -> let res = Map.lookup x (resultsMap s) in if isJust res then fst $ fromJust res else Open x) (map senName goals)
  return proof_stats
  where
    noGoalSelected = createErrorWin "Please select a goal first." []
    Theory sign nSens = th
    (axioms, goals) = partition isAxiom 
                          (prepareSenNames transSenName nSens)
    initialLogicalPart = foldl insertSentence (signToSPLogicalPart sign) (reverse axioms)
    showResMap mp = 
        '{':(foldr  (\ (k,(x,outp)) resF -> 
                             shows k . 
                             (++) ":=\n    (" .  
                             shows x . (++) ",\n     \"" .
                             (++) (unlines outp) . (++) "\")\n" . resF) id 
                    (Map.toList mp)) "}" 
  

{- |
-}
checkGoal :: SPASSResultsMap -> SPIdentifier -> Bool
checkGoal resMap goal =
  isJust g && isProved (fst $ fromJust g)
  where
    g = Map.lookup goal resMap

{- |
  A non-GUI batch mode prover. Uses default configuration for SPASS.
  The list of goals is processed sequentially. Proved goals are inserted
  as axioms.
-}
spassProveBatch :: String -- ^ theory name
                -> Theory Sign Sentence -- ^ theory consisting of a SPASS.Sign.Sign and a list of Named SPASS.Sign.Sentence
                -> IO([Proof_status ()]) -- ^ proof status for each goal
spassProveBatch thName (Theory sig nSens) =
  do pstl <- {- trace (showPretty initialLogicalPart (show goals)) -} (batchProve initialLogicalPart [] goals)
     putStrLn ("Outcome of proofs:\n" ++ unlines (map show pstl) ++ "\n")
     return pstl
  where
    batchProve _ done [] = return done
    batchProve lp done (x:xs) = do
        (err, (res, _)) <- runSpass lp emptyConfig x
	putStrLn $ show err
        -- add proved goals as axioms
        let lp' = if (isProved res) then (insertSentence lp (x{isAxiom = True})) else lp
        batchProve lp' (res:done) xs
    (axioms, goals) = partition isAxiom nSens
    initialLogicalPart = foldl insertSentence (signToSPLogicalPart sig) (reverse axioms)

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
runSpass :: SPLogicalPart -- ^ logical part containing the input Sign and axiomsand possibly goals that have been proved earlier as additional axioms
         -> SPASSConfig -- ^ configuration to use
         -> Named SPTerm -- ^ goal to prove
         -> IO (SpassProverRetval, SPASSResult) -- ^ (retval, (proof status, complete output))
runSpass lp config nGoal =
  Exception.catch (runSpassReal lp config nGoal)
    (\ exp -> return (SpassError ("Error running SPASS.\n"++show exp), 
                      (Open (senName nGoal), [])))

  where
    runSpassReal lp config nGoal = do
      -- FIXME: this should be retrieved from the user instead of being hardcoded.
      let problem = SPProblem {identifier = "hets_exported",
                               description = SPDescription {name = "hets_exported", author = "hets user", SPASS.Sign.version = Nothing, logic = Nothing, status = SPStateUnknown, desc = "", date = Nothing},
                               logicalPart = insertSentence lp nGoal}
      let filterOptions = ["-DocProof", "-Stdin", "-TimeLimit"]
      let cleanOptions = filter (\x-> not (or (map (\y-> isPrefixOf y x) filterOptions))) (extraOpts config)
      let tLimit = if isJust (timeLimit config) then fromJust (timeLimit config) else defaultTimeLimit
      let allOptions = cleanOptions ++ ["-DocProof", "-Stdin", "-TimeLimit=" ++ (show tLimit)]
      putStrLn ("running 'SPASS" ++ (concatMap (' ':) allOptions) ++ "'")
      spass <- newChildProcess "SPASS" [ChildProcess.arguments allOptions]
      -- check if SPASS is running
      e <- getToolStatus spass
      if isJust e
        then return (SpassError "Could not start SPASS. Is SPASS in your $PATH?", (Open (senName nGoal), []))
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
