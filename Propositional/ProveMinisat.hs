{- |
Module      :  $Header$
Description :  Provers for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

This is the connection of the SAT-Solver minisat to Hets
-}

module Propositional.ProveMinisat
  ( MiniSatVer (..)
  , minisatProver
  , minisatConsChecker
  ) where

import qualified Propositional.AS_BASIC_Propositional as AS_BASIC
import qualified Propositional.Conversions as Cons
import qualified Propositional.Conversions as PC
import qualified Propositional.Morphism as PMorphism
import qualified Propositional.ProverState as PState
import qualified Propositional.Sign as Sig
import Propositional.Sublogic (PropSL, top)

import Proofs.BatchProcessing

import qualified Logic.Prover as LP

import Interfaces.GenericATPState
import GUI.GenericATP

import Common.ProofTree
import qualified Common.AS_Annotation as AS_Anno
import qualified Common.Id as Id
import qualified Common.OrderedMap as OMap
import qualified Common.Result as Result
import Common.Utils (timeoutCommand)

import Control.Monad (when)
import Control.Concurrent

import Data.Char
import Data.Maybe (fromMaybe)
import Data.Time (timeToTimeOfDay, midnight)
import Data.Time.Clock

import System.Directory
import System.Exit
import System.IO
import System.Process

-- * Prover implementation

minisatHelpText :: String
minisatHelpText = "minisat is a very fast SAT-Solver \n" ++
                  "No additional Options are available" ++
                  "for it!"

data MiniSatVer = Minisat | Minisat2 deriving Show

msatName :: MiniSatVer -> String
msatName = map toLower . show

{- |
  The Prover implementation.

  Implemented are: a prover GUI, and both commandline prover interfaces.
-}
minisatProver :: MiniSatVer
  -> LP.Prover Sig.Sign AS_BASIC.FORMULA PMorphism.Morphism PropSL ProofTree
minisatProver v = LP.mkAutomaticProver (msatName v) top (minisatProveGUI v)
  $ minisatProveCMDLautomaticBatch v

{- |
   The Consistency Cheker.
-}
minisatConsChecker :: MiniSatVer
  -> LP.ConsChecker Sig.Sign AS_BASIC.FORMULA PropSL PMorphism.Morphism
     ProofTree
minisatConsChecker v = LP.mkConsChecker (msatName v) top $ consCheck v

consCheck :: MiniSatVer -> String -> LP.TacticScript
  -> LP.TheoryMorphism Sig.Sign AS_BASIC.FORMULA PMorphism.Morphism ProofTree
  -> [LP.FreeDefMorphism AS_BASIC.FORMULA PMorphism.Morphism]
  -- ^ free definitions
  -> IO (LP.CCStatus ProofTree)
consCheck v thName _ tm _ = case LP.tTarget tm of
  LP.Theory sig nSens -> do
    let axioms = getAxioms $ snd $ unzip $ OMap.toList nSens
        thName_clean = map (\ c -> if c == '/' then '_' else c) thName
        tmpFile = "/tmp/" ++ thName_clean ++ "_cc.dimacs"
        bin = msatName v
    dimacsOutput <- PC.showDIMACSProblem (thName ++ "_cc") sig
          axioms
          [(AS_Anno.makeNamed "consistency" $
            AS_BASIC.False_atom Id.nullRange)
          { AS_Anno.isAxiom = False
          , AS_Anno.isDef = False
          , AS_Anno.wasTheorem = False
          }]
    outputHf <- openFile tmpFile ReadWriteMode
    hPutStr outputHf dimacsOutput
    hClose outputHf
    (_, _, _, pid) <- runInteractiveCommand $ bin ++ " \"" ++ tmpFile ++ "\""
    exitCode <- waitForProcess pid
    removeFile tmpFile
    (res, out) <- case exitCode of
      ExitFailure 10 -> return (Just True, "consistent.")
      ExitFailure 20 -> return (Just False, "inconsistent.")
      _ -> return (Nothing, "error by calling " ++ bin ++ " " ++ thName)
    return LP.CCStatus { LP.ccResult = res
                       , LP.ccUsedTime = midnight
                       , LP.ccProofTree = ProofTree out }
  where
    getAxioms :: [LP.SenStatus AS_BASIC.FORMULA (LP.ProofStatus ProofTree)]
              -> [AS_Anno.Named AS_BASIC.FORMULA]
    getAxioms = map (AS_Anno.makeNamed "axn" . AS_Anno.sentence)
      . filter AS_Anno.isAxiom

-- ** GUI

{- |
  Invokes the generic prover GUI.
-}

minisatProveGUI :: MiniSatVer -- ^ choosen minisat version
  -> String -- ^ theory name
  -> LP.Theory Sig.Sign AS_BASIC.FORMULA ProofTree
  -> [LP.FreeDefMorphism AS_BASIC.FORMULA PMorphism.Morphism]
  -- ^ free definitions
  -> IO [LP.ProofStatus ProofTree]
  -- ^ proof status for each goal
minisatProveGUI v thName th freedefs =
  genericATPgui (atpFun v thName) True (msatName v) thName th
                freedefs emptyProofTree
{- |
  Parses a given default tactic script into a
  'Interfaces.GenericATPState.ATPTacticScript' if possible.
-}
parseminisatTacticScript :: LP.TacticScript -> ATPTacticScript
parseminisatTacticScript = parseTacticScript batchTimeLimit []

-- ** command line function

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the minisat prover.
  minisat specific functions are omitted by data type ATPFunctions.
-}
minisatProveCMDLautomaticBatch :: MiniSatVer
  -> Bool -- ^ True means include proved theorems
  -> Bool -- ^ True means save problem file
  -> MVar (Result.Result [LP.ProofStatus ProofTree])
  -- ^ used to store the result of the batch run
  -> String -- ^ theory name
  -> LP.TacticScript -- ^ default tactic script
  -> LP.Theory Sig.Sign AS_BASIC.FORMULA ProofTree
  -- ^ theory consisting of a signature and a list of Named sentences
  -> [LP.FreeDefMorphism AS_BASIC.FORMULA PMorphism.Morphism]
  -- ^ free definitions
  -> IO (ThreadId, MVar ())
  -- ^ fst: identifier of the batch thread for killing it
  -- snd: MVar to wait for the end of the thread
minisatProveCMDLautomaticBatch v inclProvedThs saveProblem_batch resultMVar
                               thName defTS th freedefs =
  genericCMDLautomaticBatch (atpFun v thName) inclProvedThs saveProblem_batch
    resultMVar (msatName v) thName
    (parseminisatTacticScript defTS) th freedefs emptyProofTree

{- |
  Record for prover specific functions. This is used by both GUI and command
  line interface.
-}
atpFun :: MiniSatVer
       -> String -- ^ Theory name
       -> ATPFunctions Sig.Sign AS_BASIC.FORMULA PMorphism.Morphism ProofTree
                       PState.PropProverState
atpFun v thName = ATPFunctions
                { initialProverState = PState.propProverState
                , goalOutput = Cons.goalDIMACSProblem thName
                , atpTransSenName = PState.transSenName
                , atpInsertSentence = PState.insertSentence
                , proverHelpText = minisatHelpText
                , runProver = runminisat v
                , batchTimeEnv = "HETS_MINISAT_BATCH_TIME_LIMIT"
                , fileExtensions = FileExtensions
                    { problemOutput = ".dimacs"
                    , proverOutput = ".minisat"
                    , theoryConfiguration = ".cminisat"}
                , createProverOptions = createminisatOptions }

{- |
  Runs minisat. minisat is assumed to reside in PATH.
-}

runminisat :: MiniSatVer -> PState.PropProverState
           -- logical part containing the input Sign and
           -- axioms and possibly goals that have been proved
           -- earlier as additional axioms
           -> GenericConfig ProofTree
           -- configuration to use
           -> Bool
           -- True means save DIMACS file
           -> String
           -- Name of the theory
           -> AS_Anno.Named AS_BASIC.FORMULA
           -- Goal to prove
           -> IO (ATPRetval, GenericConfig ProofTree)
           -- (retval, configuration with proof status and complete output)
runminisat v pState cfg saveDIMACS thName nGoal = do
  prob <- Cons.goalDIMACSProblem thName pState nGoal []
  let zFileName = "/tmp/problem_" ++ thName ++ '_' : AS_Anno.senAttr nGoal
                  ++ ".dimacs"
  when saveDIMACS
    (writeFile (thName ++ '_' : AS_Anno.senAttr nGoal ++ ".dimacs") prob)
  writeFile zFileName prob
  runStuff zFileName $ fromMaybe 100 $ timeLimit cfg
  where
    bin = msatName v
    defaultProofStatus opts =
      (LP.openProofStatus (AS_Anno.senAttr nGoal) bin
                          emptyProofTree)
      { LP.tacticScript = LP.TacticScript $ show ATPTacticScript
        { tsTimeLimit = configTimeLimit cfg
        , tsExtraOpts = opts } }
    runStuff zFileName t = do
      startTime <- getCurrentTime
      (mExit, outH, _) <- timeoutCommand t $ bin ++ " \"" ++ zFileName ++ "\""
      case mExit of
        Just exCode -> do
          let stTime = utctDayTime startTime
          endTime <- getCurrentTime
          let edTime = utctDayTime endTime
              usedTime = timeToTimeOfDay $ edTime - stTime
          out <- hGetContents outH
          return $ case exCode of
            ExitFailure 20 -> (ATPSuccess, cfg
              { proofStatus = (defaultProofStatus [])
                { LP.goalStatus = LP.Proved True
                , LP.usedAxioms = filter (/= AS_Anno.senAttr nGoal)
                  $ map AS_Anno.senAttr $ PState.initialAxioms pState
                , LP.proofTree = ProofTree out }
              , timeUsed = usedTime })
            ExitFailure 10 -> (ATPSuccess, cfg
              { proofStatus = (defaultProofStatus [])
                { LP.goalStatus = LP.Disproved
                , LP.proofTree = ProofTree out }})
            ExitSuccess -> (ATPSuccess, cfg
              { proofStatus = (defaultProofStatus [])
                { LP.goalStatus = LP.openGoalStatus
                , LP.proofTree = ProofTree "Unkown"
                , LP.usedTime = timeToTimeOfDay $ secondsToDiffTime 0 }})
            _ -> (ATPError "Internal error.", cfg
              { proofStatus = defaultProofStatus [] })
        Nothing -> return (ATPTLimitExceeded, cfg
          { proofStatus = (defaultProofStatus [])
            { LP.goalName = thName
            , LP.goalStatus = LP.openGoalStatus
            , LP.usedAxioms = []
            , LP.usedProver = bin
            , LP.proofTree = ProofTree "Timeout"
            , LP.usedTime = timeToTimeOfDay $ secondsToDiffTime 0
            , LP.tacticScript = LP.TacticScript $ show ATPTacticScript
              { tsTimeLimit = configTimeLimit cfg
              , tsExtraOpts = [] } }
          , timeLimitExceeded = True })

{- |
  Creates a list of all options the minisat prover runs with.
  Only Option is the timelimit
-}
createminisatOptions :: GenericConfig ProofTree -> [String]
createminisatOptions cfg = [show $ configTimeLimit cfg]
