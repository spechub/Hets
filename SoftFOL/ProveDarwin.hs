{- |
Module      :  ./SoftFOL/ProveDarwin.hs
Description :  Interface to the TPTP theorem prover via Darwin.
Copyright   :  (c) Heng Jiang, Uni Bremen 2004-2007
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  needs POSIX

Interface for the Darwin service, uses GUI.GenericATP.
See <http://spass.mpi-sb.mpg.de/> for details on SPASS, and
<http://combination.cs.uiowa.edu/Darwin/> for Darwin.
-}

module SoftFOL.ProveDarwin
  ( darwinProver
  , darwinCMDLautomaticBatch
  , darwinConsChecker
  , runDarwinProcess
  , ProverBinary (..)
  , darwinExe
  , tptpProvers
  , eproverOpts
  ) where

-- preliminary hacks for display of CASL models
import Logic.Prover

import SoftFOL.Sign
import SoftFOL.Translate
import SoftFOL.ProverState
import SoftFOL.EProver

import Common.AS_Annotation as AS_Anno
import qualified Common.Result as Result
import Common.ProofTree
import Common.ProverTools
import Common.SZSOntology
import Common.Utils

import Data.Char (isDigit)
import Data.List
import Data.Maybe
import Data.Time (timeToTimeOfDay)
import Data.Time.Clock (secondsToDiffTime)

import Control.Monad (when)
import qualified Control.Concurrent as Concurrent

import System.Directory
import System.Process (waitForProcess, runInteractiveCommand,
                       runProcess, terminateProcess)
import System.IO (hGetContents, openFile, hClose, IOMode (WriteMode))

import Control.Exception as Exception

import GUI.GenericATP
import Interfaces.GenericATPState
import Proofs.BatchProcessing

import qualified Data.Map as Map
import qualified Data.Set as Set

-- * Prover implementation

data ProverBinary = Darwin | DarwinFD | EDarwin | EProver | Leo | IProver
  deriving (Enum, Bounded)

tptpProvers :: [ProverBinary]
tptpProvers = [minBound .. maxBound]

proverBinary :: ProverBinary -> String
proverBinary b = darwinExe b ++
  case b of
    Darwin -> "-non-fd"
    _ -> ""

darwinExe :: ProverBinary -> String
darwinExe b = case b of
  Darwin -> "darwin"
  DarwinFD -> "darwin"
  EDarwin -> "e-darwin"
  EProver -> "eprover"
  Leo -> "leo"
  IProver -> "iproveropt"

{- | The Prover implementation. First runs the batch prover (with
  graphical feedback), then starts the GUI prover. -}
darwinProver
  :: ProverBinary -> Prover Sign Sentence SoftFOLMorphism () ProofTree
darwinProver b =
  mkAutomaticProver (darwinExe b) (proverBinary b) () (darwinGUI b)
  $ darwinCMDLautomaticBatchAux b

darwinConsChecker
  :: ProverBinary -> ConsChecker Sign Sentence () SoftFOLMorphism ProofTree
darwinConsChecker b =
  (mkUsableConsChecker (darwinExe b) (proverBinary b) () $ consCheck b)
  { ccNeedsTimer = False }

{- |
  Record for prover specific functions. This is used by both GUI and command
  line interface.
-}
atpFun :: ProverBinary  -- ^ the actual binary
  -> String -- ^ theory name
  -> ATPFunctions Sign Sentence SoftFOLMorphism ProofTree SoftFOLProverState
atpFun b thName = ATPFunctions
  { initialProverState = spassProverState
  , atpTransSenName = transSenName
  , atpInsertSentence = insertSentenceGen
  , goalOutput = showTPTPProblem thName
  , proverHelpText = "no help for darwin available"
  , batchTimeEnv = "HETS_SPASS_BATCH_TIME_LIMIT"
  , fileExtensions = FileExtensions
      { problemOutput = ".tptp"
      , proverOutput = ".spass"
      , theoryConfiguration = ".spcf" }
  , runProver = runDarwin b
  , createProverOptions = extraOpts }

-- ** GUI

{- |
  Invokes the generic prover GUI. SPASS specific functions are omitted by
  data type ATPFunctions.
-}
darwinGUI
  :: ProverBinary -- ^ the actual binary
  -> String -- ^ theory name
  -> Theory Sign Sentence ProofTree
  -- ^ theory consisting of a signature and sentences
  -> [FreeDefMorphism SPTerm SoftFOLMorphism] -- ^ freeness constraints
  -> IO [ProofStatus ProofTree] -- ^ proof status for each goal
darwinGUI b thName th freedefs =
    genericATPgui (atpFun b thName) True (proverBinary b) thName th
                  freedefs emptyProofTree

-- ** command line function

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the Darwin prover.
  Darwin specific functions are omitted by data type ATPFunctions.
-}
darwinCMDLautomaticBatch
  :: Bool -- ^ True means include proved theorems
  -> Bool -- ^ True means save problem file
  -> Concurrent.MVar (Result.Result [ProofStatus ProofTree])
  -- ^ used to store the result of the batch run
  -> String -- ^ theory name
  -> TacticScript -- ^ default tactic script
  -> Theory Sign Sentence ProofTree
  -- ^ theory consisting of a signature and sentences
  -> [FreeDefMorphism SPTerm SoftFOLMorphism] -- ^ freeness constraints
  -> IO (Concurrent.ThreadId, Concurrent.MVar ())
     {- ^ fst: identifier of the batch thread for killing it
     snd: MVar to wait for the end of the thread -}
darwinCMDLautomaticBatch = darwinCMDLautomaticBatchAux Darwin

darwinCMDLautomaticBatchAux
  :: ProverBinary -- ^ the actual binary
  -> Bool -- ^ True means include proved theorems
  -> Bool -- ^ True means save problem file
  -> Concurrent.MVar (Result.Result [ProofStatus ProofTree])
  -- ^ used to store the result of the batch run
  -> String -- ^ theory name
  -> TacticScript -- ^ default tactic script
  -> Theory Sign Sentence ProofTree
  -- ^ theory consisting of a signature and sentences
  -> [FreeDefMorphism SPTerm SoftFOLMorphism] -- ^ freeness constraints
  -> IO (Concurrent.ThreadId, Concurrent.MVar ())
     {- ^ fst: identifier of the batch thread for killing it
     snd: MVar to wait for the end of the thread -}
darwinCMDLautomaticBatchAux b inclProvedThs saveProblem_batch resultMVar
                        thName defTS th freedefs =
    genericCMDLautomaticBatch (atpFun b thName) inclProvedThs saveProblem_batch
        resultMVar (proverBinary b) thName
        (parseTacticScript batchTimeLimit [] defTS) th freedefs emptyProofTree

-- * Main prover functions

eproverOpts :: String -> String
eproverOpts verb = "-xAuto -tAuto --tptp3-format " ++ verb
  ++ " --memory-limit=2048 --soft-cpu-limit="

extras :: ProverBinary -> Bool -> String -> String
extras b cons tl = let
  tOut = " -to " ++ tl
  darOpt = "-pc false"
  fdOpt = darOpt ++ (if cons then " -pmtptp true" else "") ++ " -fd true"
  in case b of
    EProver -> eproverOpts (if cons then "-s" else "") ++ tl
    Leo -> "-t " ++ tl
    Darwin -> darOpt ++ tOut
    DarwinFD -> fdOpt ++ tOut
    EDarwin -> fdOpt ++ " -eq Axioms" ++ tOut
    IProver -> "--time_out_real " ++ tl ++ " --sat_mode true"

{- | Runs the Darwin service. The tactic script only contains a string for the
  time limit. -}
consCheck
  :: ProverBinary
  -> String
  -> TacticScript
  -> TheoryMorphism Sign Sentence SoftFOLMorphism ProofTree
  -> [FreeDefMorphism SPTerm SoftFOLMorphism] -- ^ freeness constraints
  -> IO (CCStatus ProofTree)
consCheck b thName (TacticScript tl) tm freedefs = case tTarget tm of
    Theory sig nSens -> do
        let proverStateI = spassProverState sig (toNamedList nSens) freedefs
        prob <- showTPTPProblemM thName proverStateI []
        (exitCode, out, tUsed) <-
          runDarwinProcess (darwinExe b) False (extras b True tl) thName prob
        let outState = CCStatus
               { ccResult = Just True
               , ccProofTree = ProofTree $ unlines $ exitCode : out
               , ccUsedTime = timeToTimeOfDay $ secondsToDiffTime
                            $ toInteger tUsed }
        return $ if szsProved exitCode then outState else
                    outState
                    { ccResult = if szsDisproved exitCode then Just False
                                 else Nothing }

runDarwinProcess
  :: String -- ^ binary name
  -> Bool -- ^ save problem
  -> String -- ^ options
  -> String -- ^ filename without extension
  -> String -- ^ problem
  -> IO (String, [String], Int)
runDarwinProcess bin saveTPTP options tmpFileName prob = do
  let tmpFile = basename tmpFileName ++ ".tptp"
  when saveTPTP (writeFile tmpFile prob)
  noProg <- missingExecutableInPath bin
  if noProg then
    return (bin ++ " not found. Check your $PATH", [], -1)
    else do
    timeTmpFile <- getTempFile prob tmpFile
    (_, pout, perr) <-
      executeProcess bin (words options ++ [timeTmpFile]) ""
    let l = lines $ pout ++ perr
        (res, _, tUsed) = parseOutput l
    removeFile timeTmpFile
    return (res, l, tUsed)

mkGraph :: String -> IO ()
mkGraph f = do
 fContent <- readFile f
 let fLines = lines fContent
 let ((p_set, (cs, axs)), res) =
      processProof (zipF proofInfo $ zipF conjectures axioms)
       (Set.empty, ([], [])) $ reverse fLines
     (aliases, _) = processProof alias Map.empty fLines
     same_rank = intercalate "; " $ map (\ (_, n) -> 'v' : n) $
                 filter (\ (_, n) -> Set.member n p_set
                                && isNothing (Map.lookup n aliases)) $ cs ++ axs
 case res of
  Just s -> putStrLn s
  _ -> return ()
 writeFile "/tmp/graph.dot" $ unlines ["digraph {",
  "subgraph { rank = same; " ++ same_rank ++ " }",
  (\ (_, _, d, _) -> d) . fst $ processProof (digraph p_set aliases)
   (Set.empty, Set.empty, "", Map.empty) fLines, "}"]

runEProverBuffered
  :: Bool -- ^ save problem
  -> Bool
  -> Bool
  -> String -- ^ options
  -> String -- ^ filename without extension
  -> String -- ^ problem
  -> IO (String, [String], Int)
runEProverBuffered saveTPTP graph fullgraph options tmpFileName prob = do
  s <- supportsProofObject
  let tmpFile = basename tmpFileName ++ ".tptp"
      useProofObject = s && not fullgraph
      bin = if useProofObject then "eprover"
            else "eproof"
  noProg <- missingExecutableInPath bin
  when saveTPTP (writeFile tmpFile prob)
  if noProg then return (bin ++ " not found. Check your $PATH", [], -1)
    else do
   (err, out) <-
      do
       timeTmpFile <- getTempFile prob tmpFile
       (_, out, err, _) <-
        if graph || fullgraph || not s then do
              bufferFile <- getTempFile "" "eprover-proof-buffer"
              buff <- openFile bufferFile WriteMode
              h <- runProcess bin (words options ++
                    ["--proof-object" | useProofObject] ++ [timeTmpFile])
                    Nothing Nothing Nothing (Just buff) (Just buff)
              (waitForProcess h >> removeFile timeTmpFile)
               `Exception.catch` (\ ThreadKilled -> terminateProcess h)
              hClose buff
              mkGraph bufferFile
              runInteractiveCommand $ unwords ["egrep", "axiom|SZS",
                bufferFile, "&&", "rm", "-f", bufferFile]
        else runInteractiveCommand $ unwords
             [bin, "--proof-object", options, timeTmpFile,
              "|", "egrep", "axiom|SZS", "&&", "rm", timeTmpFile]
       return (out, err)
   perr <- hGetContents err
   pout <- hGetContents out
   let l = lines $ perr ++ pout
       (res, _, tUsed) = parseOutput l
   return (res, l, tUsed)

runDarwin
  :: ProverBinary
  -> SoftFOLProverState
  {- ^ logical part containing the input Sign and axioms and possibly
  goals that have been proved earlier as additional axioms -}
  -> GenericConfig ProofTree -- ^ configuration to use
  -> Bool -- ^ True means save TPTP file
  -> String -- ^ name of the theory in the DevGraph
  -> AS_Anno.Named SPTerm -- ^ goal to prove
  -> IO (ATPRetval, GenericConfig ProofTree)
     -- ^ (retval, configuration with proof status and complete output)
runDarwin b sps cfg saveTPTP thName nGoal = do
    let bin = darwinExe b
        (options, graph, fullgraph) = case b of
          EProver ->
           let w = extraOpts cfg
           in (filter (not . (\ e -> elem e ["--graph", "--full-graph"])) w,
               elem "--graph" w, elem "--full-graph" w)
          _ -> (extraOpts cfg, False, False)
        tl = maybe "10" show $ timeLimit cfg
        extraOptions = extras b False tl
        tmpFileName = thName ++ '_' : AS_Anno.senAttr nGoal
    prob <- showTPTPProblem thName sps nGoal
      $ options ++ ["Requested prover: " ++ bin]
    (exitCode, out, tUsed) <- case b of
      EProver -> runEProverBuffered saveTPTP graph fullgraph
                  extraOptions tmpFileName prob
      _ -> runDarwinProcess bin saveTPTP extraOptions tmpFileName prob
    axs <- case b of
            EProver | szsProved exitCode ||
                      szsDisproved exitCode ->
                         case processProof axioms [] out of
                          (l, Nothing) -> return $ map fst l
                          (_, Just err) -> do
                                            putStrLn err
                                            return $ getAxioms sps
            _ -> return $ getAxioms sps
    let ctime = timeToTimeOfDay $ secondsToDiffTime $ toInteger tUsed
        (err, retval) = case () of
          _ | szsProved exitCode -> (ATPSuccess, provedStatus)
          _ | szsDisproved exitCode -> (ATPSuccess, disProvedStatus)
          _ | szsTimeout exitCode ->
              (ATPTLimitExceeded, defaultProofStatus)
          _ | szsStopped exitCode ->
              (ATPBatchStopped, defaultProofStatus)
          _ -> (ATPError exitCode, defaultProofStatus)
        defaultProofStatus =
            (openProofStatus
            (AS_Anno.senAttr nGoal) bin emptyProofTree)
                       { usedTime = ctime
                       , tacticScript = TacticScript $ show ATPTacticScript
                        {tsTimeLimit = configTimeLimit cfg,
                         tsExtraOpts = options} }

        disProvedStatus = defaultProofStatus {goalStatus = Disproved}
        provedStatus = defaultProofStatus
          { goalName = AS_Anno.senAttr nGoal
          , goalStatus = Proved True
          , usedAxioms = axs
          , usedProver = bin
          , usedTime = timeToTimeOfDay $ secondsToDiffTime $ toInteger tUsed
          }
    return (err, cfg {proofStatus = retval,
                      resultOutput = case b of
                                      EProver -> reverse out
                                      _ -> out,
                      timeUsed = ctime })

getSZSStatusWord :: String -> Maybe String
getSZSStatusWord line = case words $ fromMaybe ""
    $ stripPrefix "SZS status" $ dropWhile (`elem` "%# ") line of
  [] -> Nothing
  w : _ -> Just w

parseOutput :: [String] -> (String, Bool, Int)
  -- ^ (exit code, status found, used time)
parseOutput = foldl' checkLine ("could not determine SZS status", False, -1)
  where checkLine (exCode, stateFound, to) line =
          if isPrefixOf "Couldn't find eprover" line
             || isInfixOf "darwin -h for further information" line
                -- error by running darwin.
            then (line, stateFound, to)
            else case getSZSStatusWord line of
                Just szsState | not stateFound ->
                  (szsState, True, to)
                _ -> if "CPU  Time" `isPrefixOf` line  -- get cpu time
                  then let time = case takeWhile isDigit $ last (words line) of
                             ds@(_ : _) -> read ds
                             _ -> to
                       in (exCode, stateFound, time)
                  else (exCode, stateFound, to)
