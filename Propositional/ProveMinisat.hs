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
    (
     minisatProver,                   -- the minisat Prover
     minisatConsChecker
    )
    where

import qualified Propositional.AS_BASIC_Propositional as AS_BASIC
import qualified Propositional.Conversions as Cons
import qualified Propositional.Conversions as PC
import qualified Propositional.Morphism as PMorphism
import qualified Propositional.ProverState as PState
import qualified Propositional.Sign as Sig
import Propositional.Sublogic(PropSL,top)

import Proofs.BatchProcessing

import qualified Logic.Prover as LP

import Interfaces.GenericATPState
import GUI.GenericATP
import GUI.Utils (infoDialog)

import Common.ProofTree
import qualified Common.AS_Annotation as AS_Anno
import qualified Common.Id as Id
import qualified Common.OrderedMap as OMap
import qualified Common.Result as Result

import Control.Monad (when)
import qualified Control.Concurrent as Concurrent
import Data.Time (timeToTimeOfDay)
import System.Directory
import System.Exit
import System.IO
import System.Process

import Data.Time.Clock

import Control.Concurrent

-- * Prover implementation

minisatHelpText :: String
minisatHelpText = "minisat is a very fast SAT-Solver \n"++
                 "No additional Options are available"++
                 "for it!"

-- | the name of the prover
minisatS :: String
minisatS = "minisat"

{- |
  The Prover implementation.

  Implemented are: a prover GUI, and both commandline prover interfaces.
-}
minisatProver
  :: LP.Prover Sig.Sign AS_BASIC.FORMULA PMorphism.Morphism PropSL ProofTree
minisatProver = (LP.mkProverTemplate minisatS top minisatProveGUI)
    { LP.proveCMDLautomatic = Just $ minisatProveCMDLautomatic
    , LP.proveCMDLautomaticBatch = Just $ minisatProveCMDLautomaticBatch }

{- |
   The Consistency Cheker.
-}
minisatConsChecker :: LP.ConsChecker Sig.Sign AS_BASIC.FORMULA PropSL
                                  PMorphism.Morphism ProofTree
minisatConsChecker = LP.mkProverTemplate minisatS top consCheck

consCheck :: String -> LP.TheoryMorphism Sig.Sign AS_BASIC.FORMULA
             PMorphism.Morphism ProofTree
          -> [LP.FreeDefMorphism AS_BASIC.FORMULA PMorphism.Morphism]
          -- ^ free definitions
          -> IO([LP.ProofStatus ProofTree])
consCheck thName tm _ =
    case LP.tTarget tm of
      LP.Theory sig nSens -> do
            let axioms = getAxioms $ snd $ unzip $ OMap.toList nSens
                thName_clean = map (\c -> if c == '/' then '_' else c) thName
                tmpFile = "/tmp/" ++ thName_clean ++ "_cc.dimacs"
            dimacsOutput <-  PC.ioDIMACSProblem (thName ++ "_cc")
                             sig ( [(AS_Anno.makeNamed "myAxioms" $
                                     AS_BASIC.Implication
                                     (
                                      AS_BASIC.Conjunction
                                      (map (AS_Anno.sentence) axioms)
                                      Id.nullRange
                                     )
                                     (AS_BASIC.False_atom Id.nullRange)
                                     Id.nullRange
                                    )
                                    {
                                      AS_Anno.isAxiom = True
                                    , AS_Anno.isDef   = False
                                    , AS_Anno.wasTheorem = False
                                    }
                                   ]
                                 )[]
            outputHf <- openFile tmpFile ReadWriteMode
            hPutStr outputHf dimacsOutput
            hClose outputHf
            (_, _, _, pid) <- runInteractiveCommand
              $ "minisat \"" ++ tmpFile ++ "\""
            exitCode <- waitForProcess pid
            removeFile tmpFile
            infoDialog "consistency checker" $ case exitCode of
              ExitFailure 20 -> "consistent."
              ExitFailure 10 -> "inconsistent."
              _ -> "error by calling minisat " ++ thName
            return []

    where
        getAxioms :: [LP.SenStatus AS_BASIC.FORMULA (LP.ProofStatus ProofTree)]
                  -> [AS_Anno.Named AS_BASIC.FORMULA]
        getAxioms f = map (AS_Anno.makeNamed "consistency" . AS_Anno.sentence)
          $ filter AS_Anno.isAxiom f

-- ** GUI

{- |
  Invokes the generic prover GUI.
-}

minisatProveGUI :: String -- ^ theory name
          -> LP.Theory Sig.Sign AS_BASIC.FORMULA ProofTree
          -> [LP.FreeDefMorphism AS_BASIC.FORMULA PMorphism.Morphism]
          -- ^ free definitions
          -> IO([LP.ProofStatus ProofTree]) -- ^ proof status for each goal
minisatProveGUI thName th freedefs =
    genericATPgui (atpFun thName) True (LP.proverName minisatProver) thName th
                  freedefs emptyProofTree
{- |
  Parses a given default tactic script into a
  'Interfaces.GenericATPState.ATPTacticScript' if possible.
-}
parseminisatTacticScript :: LP.TacticScript
                        -> ATPTacticScript
parseminisatTacticScript = parseTacticScript batchTimeLimit []

-- ** command line functions

{- |
  Implementation of 'Logic.Prover.proveCMDLautomatic' which provides an
  automatic command line interface for a single goal.
  SPASS specific functions are omitted by data type ATPFunctions.
-}
minisatProveCMDLautomatic ::
           String -- ^ theory name
        -> LP.TacticScript -- ^ default tactic script
        -> LP.Theory Sig.Sign AS_BASIC.FORMULA ProofTree
        -- ^ theory consisting of a signature and a list of Named sentence
        -> [LP.FreeDefMorphism AS_BASIC.FORMULA PMorphism.Morphism]
        -- ^ free definitions
        -> IO (Result.Result ([LP.ProofStatus ProofTree]))
           -- ^ Proof status for goals and lemmas
minisatProveCMDLautomatic thName defTS th freedefs =
    genericCMDLautomatic (atpFun thName) (LP.proverName minisatProver) thName
        (parseminisatTacticScript defTS) th freedefs emptyProofTree

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the minisat prover.
  minisat specific functions are omitted by data type ATPFunctions.
-}
minisatProveCMDLautomaticBatch ::
           Bool -- ^ True means include proved theorems
        -> Bool -- ^ True means save problem file
        -> Concurrent.MVar (Result.Result [LP.ProofStatus ProofTree])
           -- ^ used to store the result of the batch run
        -> String -- ^ theory name
        -> LP.TacticScript -- ^ default tactic script
        -> LP.Theory Sig.Sign AS_BASIC.FORMULA ProofTree
        -- ^ theory consisting of a signature and a list of Named sentences
        -> [LP.FreeDefMorphism AS_BASIC.FORMULA PMorphism.Morphism]
        -- ^ free definitions
        -> IO (Concurrent.ThreadId,Concurrent.MVar ())
           -- ^ fst: identifier of the batch thread for killing it
           --   snd: MVar to wait for the end of the thread
minisatProveCMDLautomaticBatch inclProvedThs saveProblem_batch resultMVar
                        thName defTS th freedefs =
    genericCMDLautomaticBatch (atpFun thName) inclProvedThs saveProblem_batch
        resultMVar (LP.proverName minisatProver) thName
        (parseminisatTacticScript defTS) th freedefs emptyProofTree

{- |
  Record for prover specific functions. This is used by both GUI and command
  line interface.
-}
atpFun :: String            -- Theory name
  -> ATPFunctions Sig.Sign AS_BASIC.FORMULA PMorphism.Morphism ProofTree
     PState.PropProverState
atpFun thName = ATPFunctions
                { initialProverState = PState.propProverState
                , goalOutput         = Cons.goalDIMACSProblem thName
                , atpTransSenName    = PState.transSenName
                , atpInsertSentence  = PState.insertSentence
                , proverHelpText     = minisatHelpText
                , runProver          = runminisat
                , batchTimeEnv       = "HETS_MINISAT_BATCH_TIME_LIMIT"
                , fileExtensions     = FileExtensions
                    { problemOutput = ".dimacs"
                    , proverOutput = ".minisat"
                    , theoryConfiguration = ".cminisat"}
                , createProverOptions = createminisatOptions }

{- |
  Runs minisat. minisat is assumed to reside in PATH.
-}

runminisat :: PState.PropProverState
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
           -> IO (ATPRetval
                 , GenericConfig ProofTree
                 )
           -- (retval, configuration with proof status and complete output)
runminisat pState cfg saveDIMACS thName nGoal =
    do
      prob <- Cons.goalDIMACSProblem thName pState nGoal []
      let zFileName = "/tmp/problem_" ++ thName ++ '_' : AS_Anno.senAttr nGoal
            ++ ".dimacs"
      when saveDIMACS
               (writeFile (thName ++ '_' : AS_Anno.senAttr nGoal ++ ".dimacs")
                          prob)
      writeFile zFileName prob
      retVal <- case timeLimit cfg of
                  Nothing -> runStuff zFileName
                  Just t  -> timeWatch t $ runStuff zFileName
      --removeFile zFileName
      return retVal
    where
      defaultProofStatus opts =
          (LP.openProofStatus (AS_Anno.senAttr nGoal)
             (LP.proverName minisatProver) emptyProofTree)
          {LP.tacticScript = LP.TacticScript $ show $ ATPTacticScript
                             {tsTimeLimit = configTimeLimit cfg,
                              tsExtraOpts = opts} }

      timeWatch time process =
        do
          mvar <- newEmptyMVar
          tid1 <- forkIO $ do z <- process
                              putMVar mvar (Just z)
          tid2 <- forkIO $ do threadDelay (time * 1000000)
                              putMVar mvar Nothing
          res <- takeMVar mvar
          case res of
            Just z -> do
                     killThread tid2 `catch` (\e -> putStrLn (show e))
                     return z
            Nothing -> do
                     killThread tid1 `catch` (\e -> putStrLn (show e))
                     return (ATPTLimitExceeded,
                             cfg
                             {
                               proofStatus =
                                   (defaultProofStatus [])
                                   {
                                     LP.goalName = thName
                                   , LP.goalStatus = LP.openGoalStatus
                                   , LP.usedAxioms = []
                                   , LP.usedProver = LP.proverName minisatProver
                                   , LP.proofTree  = ProofTree "Timeout"
                                   , LP.usedTime = timeToTimeOfDay $
                                                   secondsToDiffTime 0
                                   , LP.tacticScript  = LP.TacticScript $ show
                                       $ ATPTacticScript
                                       { tsTimeLimit = configTimeLimit cfg
                                       , tsExtraOpts = []}
                                   }
                             , timeLimitExceeded = True
                             })
      runStuff zFileName =
          do
            (_, outHandle, _, pid) <- runInteractiveCommand
              $ "minisat \"" ++ zFileName ++ "\""
            startTime <- getCurrentTime
            let stTime = utctDayTime startTime
            exCode <- waitForProcess pid
            endTime <- getCurrentTime
            let edTime = utctDayTime endTime
            let usedTime = timeToTimeOfDay $ edTime - stTime
            out <- hGetContents outHandle
            case exCode of
              ExitFailure 20 -> do
                    let usedAxs = map (AS_Anno.senAttr)
                          $ PState.initialAxioms pState
                    return (ATPSuccess, cfg
                      { proofStatus = (defaultProofStatus [])
                          { LP.goalStatus = LP.Proved $ Nothing
                          , LP.usedAxioms = filter (/= AS_Anno.senAttr nGoal)
                                            usedAxs
                          , LP.proofTree = ProofTree out }
                      , timeUsed = usedTime })
              ExitFailure 10 -> return (ATPSuccess, cfg
                { proofStatus = (defaultProofStatus [])
                  { LP.goalStatus = LP.Disproved
                  , LP.proofTree  = ProofTree out }})
              ExitSuccess -> return (ATPSuccess, cfg
                { proofStatus = (defaultProofStatus [])
                   { LP.goalStatus = LP.openGoalStatus
                   , LP.proofTree  = ProofTree "Unkown"
                   , LP.usedTime = timeToTimeOfDay $ secondsToDiffTime 0 }})
              _ -> return (ATPError "Internal error.", cfg
                     { proofStatus = defaultProofStatus [] })

{- |
  Creates a list of all options the minisat prover runs with.
  Only Option is the timelimit
-}
createminisatOptions :: GenericConfig ProofTree -> [String]
createminisatOptions cfg =
    [show $ configTimeLimit cfg]
