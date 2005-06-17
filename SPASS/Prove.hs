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

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel

{- |
  Represents a prover configuration used when proving a goal.
-}
data SPASSConfig = SPASSConfig { -- | time limit in seconds passed to SPASS via -TimeLimit. Default will be used if Nothing.
                                 timeLimit :: Maybe Int,
                                 -- | extra options passed verbatimely to SPASS. -TimeLimit and -DocProof will be overridden.
                                 extraOpts :: [String]
                               } deriving (Eq, Ord, Show)

{- |
  Creates an empty SPASSConfig. Default time limit and no extra options.
-}
emptySpassConfig :: SPASSConfig
emptySpassConfig = SPASSConfig {timeLimit = Nothing,
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
                            else Map.insert k (f emptySpassConfig) m

{- |
  Performs a lookup on the ConfigsMap. Returns the config for the goal or an
  empty config if none is set yet.
-}
getConfig :: SPIdentifier -> SPASSConfigsMap -> SPASSConfig
getConfig id m = if (isJust lookupId)
                   then fromJust lookupId
                   else emptySpassConfig
  where
    lookupId = Map.lookup id m

{- |
  Default time limit.
-}
defaultTimeLimit :: Int
defaultTimeLimit = 60

{- |
  Represents the result of a prover run.
-}
type SPASSResult = (Proof_status (), [String], [String])

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
data State = State { currentGoal :: Maybe String,
                     configsMap :: SPASSConfigsMap,
                     resultsMap :: SPASSResultsMap
                   } deriving (Eq, Show)

{- |
  Creates an empty State.
-}
emptyState :: State
emptyState = State {currentGoal = Nothing,
                    configsMap = emptyConfigsMap,
                    resultsMap = emptyResultsMap}

{- |
  Not yet implemented.
-}
spassProver :: Prover Sign Sentence ()
spassProver =
  Prover { prover_name = "SPASS",
           prover_sublogic = "SPASS",
           prove = spassProve
         }

{- |
  Invokes the prover GUI. Not yet implemented.
-}
spassProve :: String -- ^ theory name
           -> Theory Sign Sentence -- ^ theory consisting of a SPASS.Sign.Sign and a list of Named SPASS.Sign.Sentence
           -> IO([Proof_status ()]) -- ^ proof status for each goal
spassProve thName (Theory sig nSens) =
  return []
  where
    (axioms, goals) = partition isAxiom nSens
    initialLogicalPart = signToSPLogicalPart sig

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
