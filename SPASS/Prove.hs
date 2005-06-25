{- |
Module      :  $Header$
Copyright   :  (c) Rene Wagner, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rwagner@tzi.de
Stability   :  provisional
Portability :  needs POSIX

Interface for the SPASS theorem prover.
   See <http://spass.mpi-sb.mpg.de/> for details on SPASS.

-}

module SPASS.Prove where

import Logic.Prover
import SPASS.Sign
import SPASS.Conversions
import SPASS.Print

import Common.AS_Annotation
import Common.PrettyPrint

import ChildProcess
import System.Posix
import Text.Regex
import List
import Maybe
import HTk
import SpinButton
import Data.IORef

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel

{- |
  Represents a prover configuration used when proving a goal.
-}
data SPASSConfig = SPASSConfig { -- | time limit in seconds passed to SPASS via -TimeLimit. Default will be used if Nothing.
                                 timeLimit :: Maybe Int,
                                 -- | extra options passed verbatimely to SPASS. -DocProof, -Stdin, and -TimeLimit will be overridden.
                                 extraOpts :: [String]
                               } deriving (Eq, Ord, Show)

{- |
  Creates an empty SPASSConfig. Default time limit and no extra options.
-}
emptyConfig :: SPASSConfig
emptyConfig = SPASSConfig {timeLimit = Nothing,
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
defaultTimeLimit = 60

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

{- |
  Represents the global state of the prover GUI.
-}
data State = State { currentGoal :: Maybe SPIdentifier,
                     theory :: Theory Sign Sentence,
                     configsMap :: SPASSConfigsMap,
                     resultsMap :: SPASSResultsMap
                   }

{- |
  Creates an initial State around a Theory.
-}
initialState :: Theory Sign Sentence -> SPASS.Prove.State
initialState th = State {currentGoal = Nothing,
                         theory = th,
                         configsMap = emptyConfigsMap,
                         resultsMap = emptyResultsMap}

{- |
  Currently implemented as a batch mode prover only.
-}
spassProver :: Prover Sign Sentence ()
spassProver =
  Prover { prover_name = "SPASS",
           prover_sublogic = "SPASS",
           prove = spassProveBatch
         }

{- |
  Helper function to check if a goal has been proved.
-}
isProved :: (Proof_status a) -> Bool
isProved (Proved _ _ _ _ _) = True
isProved _ = False

{- |
  Invokes the prover GUI. Not yet fully implemented.
-}
spassProveGUI :: String -- ^ theory name
              -> Theory Sign Sentence -- ^ theory consisting of a SPASS.Sign.Sign and a list of Named SPASS.Sign.Sentence
              -> IO([Proof_status ()]) -- ^ proof status for each goal
spassProveGUI thName th = do
  state <- newIORef $ initialState th
  return []
  

{- |
  A non-GUI batch mode prover. Uses default configuration for SPASS.
  The list of goals is processed sequentially. Proved goals are inserted
  as axioms.
-}
spassProveBatch :: String -- ^ theory name
                -> Theory Sign Sentence -- ^ theory consisting of a SPASS.Sign.Sign and a list of Named SPASS.Sign.Sentence
                -> IO([Proof_status ()]) -- ^ proof status for each goal
spassProveBatch thName (Theory sig nSens) =
  batchProve initialLogicalPart [] goals
  where
    batchProve _ done [] = return done
    batchProve lp done (x:xs) = do
        (res, _) <- runSpass lp emptyConfig x
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
parseSpassOutput spass = parseIt (Nothing, [], [])
  where
    parseIt (res, usedAxioms, output) = do
      line <- readMsg spass
      let resMatch = matchRegex re_sb line
      let res' = if isJust resMatch then (Just $ head $ fromJust resMatch) else res
      let usedAxiomsMatch = matchRegex re_ua line
      let usedAxioms' = if isJust usedAxiomsMatch then (words $ head $ fromJust usedAxiomsMatch) else usedAxioms
      if isJust (matchRegex re_stop line)
        then
          return (res', usedAxioms', output ++ [line])
        else
          parseIt (res', usedAxioms', output ++ [line])
    re_stop = mkRegex ".*SPASS-STOP.*"
    re_sb = mkRegex "SPASS beiseite: (.*)$"
    re_ua = mkRegex "Formulae used in the proof.*:(.*)$"

{- |
  Runs SPASS. SPASS is assumed to reside in PATH.
-}
runSpass :: SPLogicalPart -- ^ logical part containing the input Sign and axiomsand possibly goals that have been proved earlier as additional axioms
         -> SPASSConfig -- ^ configuration to use
         -> Named SPTerm -- ^ goal to prove
         -> IO SPASSResult -- ^ (proof status, complete output)
runSpass lp config nGoal = do
  -- FIXME: this should be retrieved from the user instead of being hardcoded.
  let problem = SPProblem {identifier = "hets_exported",
                           description = SPDescription {name = "hets_exported", author = "hets user", SPASS.Sign.version = Nothing, logic = Nothing, status = SPStateUnknown, desc = "", date = Nothing},
                           logicalPart = insertSentence lp nGoal}
  let filterOptions = ["-DocProof", "-Stdin", "-TimeLimit"]
  let cleanOptions = filter (\x-> not (or (map (\y-> isPrefixOf y x) filterOptions))) (extraOpts config)
  let tLimit = if isJust (timeLimit config) then fromJust (timeLimit config) else defaultTimeLimit
  let allOptions = cleanOptions ++ ["-DocProof", "-Stdin", "-TimeLimit=" ++ (show tLimit)]
  putStrLn ("running 'SPASS" ++ (concatMap (' ':) allOptions))
  spass <- newChildProcess "SPASS" [ChildProcess.arguments allOptions]
  -- FIXME: use printText0 instead. but where to get an instance of GlobalAnnos from?
  sendMsg spass (showPretty problem "")
  (res, usedAxioms, output) <- parseSpassOutput spass
  return (proof_status res usedAxioms cleanOptions, output)
  where
    proof_status res usedAxioms options
      | isJust res && elem (fromJust res) proved = Proved (senName nGoal) usedAxioms "SPASS" () (Tactic_script (concatMap (' ':) options))
      | isJust res && elem (fromJust res) disproved = Disproved (senName nGoal)
      | otherwise = Open (senName nGoal)
    proved = ["Proof found."]
    disproved = ["Completion found."]

{- |
  Test function. Currently it runs SPASS, parses the output, and outputs relevant parts to stdout.
-}
testSpass :: String -> IO ()
testSpass file = do
  spass <- newChildProcess "SPASS" [ChildProcess.arguments ["-TimeLimit=10", "-DocProof", file]]
--  sendMsg spass "bar"
  _ <- waitForChildProcess spass
  (res, usedAxioms, output) <- parseSpassOutput spass
  putStrLn $ show (res, usedAxioms)
--  mapM_ putStrLn output

{- |
  GUI prototype. Will later be moved to spassProveGUI.
-}
gui :: IO ()
gui =
  do main <- initHTk [text "SPASS Prover"]
     -- left frame
     left <- newFrame main []
     grid left [GridPos (0,0)]
     lb <- newListBox left [value goals, bg "white",
                            size (15,10), selectMode Single] :: IO (ListBox String)
     pack lb [Side AtLeft, Fill Y]
     sb <- newScrollBar left []
     pack sb [Side AtRight, Fill Y]
     lb # scrollbar Vertical sb
     -- right frame
     right <- newFrame main []
     grid right [GridPos (1,0)]
     spacer <- newLabel right [text "   "]
     grid spacer [GridPos (0,1), Sticky W, Sticky W]
     l1 <- newLabel right [text "Options:"]
     grid l1 [GridPos (0,0), Columnspan 2, Sticky W]
     l2 <- newLabel right [text "TimeLimit"]
     grid l2 [GridPos (1,1), Sticky W]
     (timeEntry :: Entry Int) <- newEntry right [width 4, value (60::Int)]
     grid timeEntry [GridPos (3,1), Sticky W]
     timeSpinner <- newSpinButton right (\_->return ()) []
     grid timeSpinner [GridPos (3,1), Sticky E]
     l3 <- newLabel right [text "Extra Options:"]
     grid l3 [GridPos (1,2), Sticky W]
     (optionsEntry :: Entry String) <- newEntry right [width 30]
     grid optionsEntry [GridPos (1,3), Columnspan 2, Sticky W]
     proveButton <- newButton right [text "Prove"]
     grid proveButton [GridPos (2,4), Columnspan 2, Sticky E]
     l4 <- newLabel right [text "Results:"]
     grid l4 [GridPos (0,5), Columnspan 2, Sticky W]
     l5 <- newLabel right [text "Status"]
     grid l5 [GridPos (1,6), Sticky W]
     statusLabel <- newLabel right [text "Open"]
     grid statusLabel [GridPos (2,6), Sticky W]
     detailsButton <- newButton right [text "Show Details"]
     grid detailsButton [GridPos (2,7), Columnspan 2, Sticky E]
     -- bottom frame
     bottom <- newFrame main []
     grid bottom [GridPos (0,1), Columnspan 2]
     exitButton <- newButton bottom [text "Exit Prover"]
     pack exitButton [Side AtRight]
     -- events
     prove <- clicked proveButton
     exit <- clicked exitButton
     (select, _) <- bindSimple lb (ButtonPress (Just 1))
     -- event handlers
     spawnEvent 
       (forever
         ((select >> always
             (do sel <- getSelection lb
                 putStrLn  (show (sel:: Maybe [Int]))))
         +> (prove >>> do sel <- getSelection lb
                          putStrLn  (show (sel:: Maybe [Int]))
                          done)
         +> (exit >>> destroy main)))
--     sync (click >>> done)
--     sel <- getSelection lb-- :: IO (Maybe [Int])
     --let sel_ = (if isJust sel then (goals !! (fromJust sel)) else "Nothing")
--     putStrLn (show (sel:: Maybe [Int]))
--     destroy main
     finishHTk
  where
    goals = map (("goal " ++) . show) [1..8]
