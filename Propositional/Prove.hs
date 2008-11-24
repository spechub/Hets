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

module Propositional.Prove
    (
     zchaffProver,                   -- the zChaff II Prover
     propConsChecker
    )
    where

import qualified Propositional.AS_BASIC_Propositional as AS_BASIC
import qualified Propositional.Conversions as Cons
import qualified Propositional.Conversions as PC
import qualified Propositional.Morphism as PMorphism
import qualified Propositional.ProverState as PState
import qualified Propositional.Sign as Sig
import Propositional.Sublogic(PropSL,top)
import Propositional.ChildMessage

import Proofs.BatchProcessing

import qualified Logic.Prover as LP

import qualified GUI.GenericATPState as ATPState
import GUI.GenericATP
import GUI.Utils (infoDialog)

import HTk
import ChildProcess as CP

import Common.ProofTree
import Common.Utils (readMaybe)
import qualified Common.AS_Annotation as AS_Anno
import qualified Common.Id as Id
import qualified Common.OrderedMap as OMap
import qualified Common.Result as Result

import qualified Control.Concurrent as Concurrent
import qualified Control.Exception as Exception
import Data.Char
import Data.List
import Data.Maybe
import Data.Time (TimeOfDay,timeToTimeOfDay)
import System.Directory
import System.Cmd
import System.Exit
import System.IO
import Text.Regex



-- * Prover implementation

zchaffHelpText :: String
zchaffHelpText = "Zchaff is a very fast SAT-Solver \n"++
                 "No additional Options are available"++
                 "for it!"

-- | the name of the prover
zchaffS :: String
zchaffS = "zchaff"

{- |
  The Prover implementation.

  Implemented are: a prover GUI, and both commandline prover interfaces.
-}
zchaffProver
  :: LP.Prover Sig.Sign AS_BASIC.FORMULA PMorphism.Morphism PropSL ProofTree
zchaffProver = (LP.mkProverTemplate zchaffS top zchaffProveGUI)
    { LP.proveCMDLautomatic = Just $ zchaffProveCMDLautomatic
    , LP.proveCMDLautomaticBatch = Just $ zchaffProveCMDLautomaticBatch }

{- |
   The Consistency Cheker.
-}
propConsChecker :: LP.ConsChecker Sig.Sign AS_BASIC.FORMULA PropSL
                                  PMorphism.Morphism ProofTree
propConsChecker = LP.mkProverTemplate zchaffS top consCheck

consCheck :: String -> LP.TheoryMorphism Sig.Sign AS_BASIC.FORMULA
             PMorphism.Morphism ProofTree
          -> [LP.FreeDefMorphism AS_BASIC.FORMULA PMorphism.Morphism] -- ^ free definitions
          -> IO([LP.Proof_status ProofTree])
consCheck thName tm _ =
    case LP.t_target tm of
      LP.Theory sig nSens -> do
            let axioms = getAxioms $ snd $ unzip $ OMap.toList nSens
                tmpFile = "/tmp/" ++ (thName ++ "_cc.dimacs")
                resultFile = tmpFile ++ ".result"
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
            exitCode <- system ("zchaff " ++ tmpFile ++ " >> " ++ resultFile)
            removeFile tmpFile
            if exitCode /= ExitSuccess then
                infoDialog "consistency checker"
                          ("error by call zchaff " ++ thName)
               else do
                   resultHf <- openFile resultFile ReadMode
                   isSAT <- searchResult resultHf
                   hClose resultHf
                   removeFile resultFile
                   if isSAT then
                       infoDialog "consistency checker"
                          ("consistent.")
                     else
                         infoDialog "consistency checker"
                          ("inconsistent.")
            return []

    where
        getAxioms :: [LP.SenStatus AS_BASIC.FORMULA (LP.Proof_status ProofTree)]
                  -> [AS_Anno.Named AS_BASIC.FORMULA]
        getAxioms f = map (AS_Anno.makeNamed "consistency" . AS_Anno.sentence) $ filter AS_Anno.isAxiom f

        searchResult :: Handle -> IO Bool
        searchResult hf = do
            eof <- hIsEOF hf
            if eof then
                return False
              else
               do
                line <- hGetLine hf
                putStrLn line
                if line == "RESULT:\tUNSAT" then
                      return True
                  else if line == "RESULT:\tSAT" then
                          return False
                         else searchResult hf

-- ** GUI

{- |
  Invokes the generic prover GUI.
-}
zchaffProveGUI :: String -- ^ theory name
          -> LP.Theory Sig.Sign AS_BASIC.FORMULA ProofTree
          -> [LP.FreeDefMorphism AS_BASIC.FORMULA PMorphism.Morphism] -- ^ free definitions
          -> IO([LP.Proof_status ProofTree]) -- ^ proof status for each goal
zchaffProveGUI thName th freedefs =
    genericATPgui (atpFun thName) True (LP.prover_name zchaffProver) thName th
                  freedefs emptyProofTree
{- |
  Parses a given default tactic script into a
  'GUI.GenericATPState.ATPTactic_script' if possible.
-}
parseZchaffTactic_script :: LP.Tactic_script
                        -> ATPState.ATPTactic_script
parseZchaffTactic_script =
    parseTactic_script batchTimeLimit

{- |
  Parses a given default tactic script into a
  'GUI.GenericATPState.ATPTactic_script' if possible. Otherwise a default
  prover's tactic script is returned.
-}
parseTactic_script :: Int -- ^ default time limit (standard:
                          -- 'Proofs.BatchProcessing.batchTimeLimit')
                   -> LP.Tactic_script
                   -> ATPState.ATPTactic_script
parseTactic_script tLimit (LP.Tactic_script ts) =
    maybe (ATPState.ATPTactic_script { ATPState.ts_timeLimit = tLimit,
                                       ATPState.ts_extraOpts = [] })
           id $ readMaybe ts

-- ** command line functions

{- |
  Implementation of 'Logic.Prover.proveCMDLautomatic' which provides an
  automatic command line interface for a single goal.
  SPASS specific functions are omitted by data type ATPFunctions.
-}
zchaffProveCMDLautomatic ::
           String -- ^ theory name
        -> LP.Tactic_script -- ^ default tactic script
        -> LP.Theory Sig.Sign AS_BASIC.FORMULA ProofTree  -- ^ theory consisting of a
                                -- signature and a list of Named sentence
        -> [LP.FreeDefMorphism AS_BASIC.FORMULA PMorphism.Morphism] -- ^ free definitions
        -> IO (Result.Result ([LP.Proof_status ProofTree]))
           -- ^ Proof status for goals and lemmas
zchaffProveCMDLautomatic thName defTS th freedefs =
    genericCMDLautomatic (atpFun thName) (LP.prover_name zchaffProver) thName
        (parseZchaffTactic_script defTS) th freedefs emptyProofTree

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the zchaff prover.
  zchaff specific functions are omitted by data type ATPFunctions.
-}
zchaffProveCMDLautomaticBatch ::
           Bool -- ^ True means include proved theorems
        -> Bool -- ^ True means save problem file
        -> Concurrent.MVar (Result.Result [LP.Proof_status ProofTree])
           -- ^ used to store the result of the batch run
        -> String -- ^ theory name
        -> LP.Tactic_script -- ^ default tactic script
        -> LP.Theory Sig.Sign AS_BASIC.FORMULA ProofTree -- ^ theory consisting of a
           --   signature and a list of Named sentences
        -> [LP.FreeDefMorphism AS_BASIC.FORMULA PMorphism.Morphism] -- ^ free definitions
        -> IO (Concurrent.ThreadId,Concurrent.MVar ())
           -- ^ fst: identifier of the batch thread for killing it
           --   snd: MVar to wait for the end of the thread
zchaffProveCMDLautomaticBatch inclProvedThs saveProblem_batch resultMVar
                        thName defTS th freedefs =
    genericCMDLautomaticBatch (atpFun thName) inclProvedThs saveProblem_batch
        resultMVar (LP.prover_name zchaffProver) thName
        (parseZchaffTactic_script defTS) th freedefs emptyProofTree

{- |
  Record for prover specific functions. This is used by both GUI and command
  line interface.
-}
atpFun :: String            -- Theory name
       -> ATPState.ATPFunctions Sig.Sign AS_BASIC.FORMULA PMorphism.Morphism ProofTree PState.PropProverState
atpFun thName = ATPState.ATPFunctions
                {
                  ATPState.initialProverState = PState.propProverState
                , ATPState.goalOutput         = Cons.goalDIMACSProblem thName
                , ATPState.atpTransSenName    = PState.transSenName
                , ATPState.atpInsertSentence  = PState.insertSentence
                , ATPState.proverHelpText     = zchaffHelpText
                , ATPState.runProver          = runZchaff
                , ATPState.batchTimeEnv       = "HETS_ZCHAFF_BATCH_TIME_LIMIT"
                , ATPState.fileExtensions     = ATPState.FileExtensions{ATPState.problemOutput = ".dimacs",
                                                                        ATPState.proverOutput = ".zchaff",
                                                                        ATPState.theoryConfiguration = ".czchaff"}
                , ATPState.createProverOptions = createZchaffOptions
                }

{- |
  Runs zchaff. zchaff is assumed to reside in PATH.
-}

runZchaff :: PState.PropProverState
           -- logical part containing the input Sign and
           -- axioms and possibly goals that have been proved
           -- earlier as additional axioms
           -> ATPState.GenericConfig ProofTree
           -- configuration to use
           -> Bool
           -- True means save DIMACS file
           -> String
           -- Name of the theory
           -> AS_Anno.Named AS_BASIC.FORMULA
           -- Goal to prove
           -> IO (ATPState.ATPRetval
                 , ATPState.GenericConfig ProofTree
                 )
           -- (retval, configuration with proof status and complete output)
runZchaff pState cfg saveDIMACS thName nGoal =
    do
      prob <- Cons.goalDIMACSProblem thName pState nGoal []
      when saveDIMACS
               (writeFile (thName++'_':AS_Anno.senAttr nGoal++".dimacs")
                          prob)
      (writeFile (zFileName)
                 prob)
      zchaff <- newChildProcess "zchaff" [CP.arguments allOptions]
      Exception.catch (runZchaffReal zchaff)
                   (\ excep -> do
                      -- kill zchaff process
                      destroy zchaff
                      _ <- waitForChildProcess zchaff
                      deleteJunk
                      excepToATPResult (LP.prover_name zchaffProver) nGoal excep)
    where
      deleteJunk = do
        catch (removeFile zFileName) (const $ return ())
        catch (removeFile "resolve_trace") (const $ return ())
      zFileName = "/tmp/problem_"++thName++'_':AS_Anno.senAttr nGoal++".dimacs"
      allOptions = zFileName : (createZchaffOptions cfg)
      runZchaffReal zchaff =
          do
                zchaffOut <- parseIt zchaff isEnd
                (res, usedAxs, output, tUsed) <- analyzeZchaff zchaffOut pState
                let (err, retval) = proof_stat res usedAxs [] (head output)
                deleteJunk
                return (err,
                        cfg{ATPState.proof_status = retval,
                            ATPState.resultOutput = output,
                            ATPState.timeUsed     = tUsed})
                where
                  proof_stat res usedAxs options out
                           | isJust res && elem (fromJust res) proved =
                               (ATPState.ATPSuccess,
                                (defaultProof_status options)
                                {LP.goalStatus = LP.Proved $ Nothing
                                , LP.usedAxioms = filter (/=(AS_Anno.senAttr nGoal)) usedAxs
                                , LP.proofTree = ProofTree $ out })
                           | isJust res && elem (fromJust res) disproved =
                               (ATPState.ATPSuccess,
                                (defaultProof_status options) {LP.goalStatus = LP.Disproved} )
                           | isJust res && elem (fromJust res) timelimit =
                               (ATPState.ATPTLimitExceeded, defaultProof_status options)
                           | isNothing res =
                               (ATPState.ATPError "Internal error.", defaultProof_status options)
                           | otherwise = (ATPState.ATPSuccess, defaultProof_status options)
                  defaultProof_status opts =
                      (LP.openProof_status (AS_Anno.senAttr nGoal) (LP.prover_name zchaffProver)
                                        emptyProofTree)
                      {LP.tacticScript = LP.Tactic_script $ show $ ATPState.ATPTactic_script
                                         {ATPState.ts_timeLimit = configTimeLimit cfg,
                                          ATPState.ts_extraOpts = opts} }

proved :: [String]
proved = ["Proof found."]
disproved :: [String]
disproved = ["Completion found."]
timelimit :: [String]
timelimit = ["Ran out of time."]

-- | analysis of output
analyzeZchaff :: String
              ->  PState.PropProverState
              -> IO (Maybe String, [String], [String], TimeOfDay)
analyzeZchaff str pState =
    let
        str' = foldr (\ch li -> if ch == '\x9'
                                then ""++li
                                else ch:li) "" str
        str2 = foldr (\ch li -> if ch == '\x9'
                                then "        "++li
                                else ch:li) "" str
        output = [str2]
        unsat  = (\xv ->
                      case xv of
                        Just _  -> True
                        Nothing -> False
            ) $ matchRegex re_UNSAT str'
        sat    = (\xv ->
                      case xv of
                        Just _  -> True
                        Nothing -> False
                    ) $ matchRegex re_SAT   str'
        timeLine = (\xv ->
                      case xv of
                        Just yv  -> head yv
                        Nothing  -> "0"
                    ) $ matchRegex re_TIME str'
        timeout =  ((\xv ->
                    case xv of
                      Just _  -> True
                      Nothing -> False
                   ) $ matchRegex re_end_to str')
                  ||
                  ((\xv ->
                   case xv of
                     Just _  -> True
                     Nothing -> False
                  ) $ matchRegex re_end_mo str')
        time   = calculateTime timeLine
        usedAx = map (AS_Anno.senAttr) $ PState.initialAxioms pState
    in
      if timeout
      then
          return (Just $ head timelimit, usedAx, output, time)
          else
              if (sat && (not unsat))
              then
                  return (Just $ head $ disproved, usedAx, output, time)
              else if ((not sat) && unsat)
                   then
                       return (Just $ head $ proved, usedAx, output, time)
                   else
                       do
                         return (Nothing, usedAx, output, time)

-- | Calculated the time need for the proof in seconds
calculateTime :: String -> TimeOfDay
calculateTime timeLine =
    timeToTimeOfDay $ realToFrac $ (maybe
         (error $ "calculateTime " ++ timeLine) id $ readMaybe timeLine
             :: Double)

re_UNSAT :: Regex
re_UNSAT = mkRegex "(.*)RESULT:UNSAT(.*)"
re_SAT :: Regex
re_SAT   = mkRegex "(.*)RESULT:SAT(.*)"
re_TIME :: Regex
re_TIME  = mkRegex "Total Run Time(.*)"

-- | We are searching for Flotter needed to determine the end of input
isEnd :: String -> Bool
isEnd inS = ((\xv ->
                 case xv of
                   Just _  -> True
                   Nothing -> False
            ) $ matchRegex re_end inS)
            ||
            ((\xv ->
                 case xv of
                   Just _  -> True
                   Nothing -> False
            ) $ matchRegex re_end_to inS)
            ||
            ((\xv ->
                 case xv of
                   Just _  -> True
                   Nothing -> False
            ) $ matchRegex re_end_mo inS)

re_end :: Regex
re_end = mkRegex "(.*)RESULT:(.*)"
re_end_to :: Regex
re_end_to = mkRegex "(.*)TIME OUT(.*)"
re_end_mo :: Regex
re_end_mo = mkRegex "(.*)MEM OUT(.*)"

-- | Converts a thrown exception into an ATP result (ATPRetval and proof tree).
excepToATPResult :: String
                 -- ^ name of running prover
                 -> AS_Anno.Named AS_BASIC.FORMULA
                 -- ^ goal to prove
                 -> Exception.Exception
                 -- ^ occured exception
                 -> IO (ATPState.ATPRetval,
                        ATPState.GenericConfig ProofTree)
                    -- ^ (retval,
                    -- configuration with proof status and complete output)
excepToATPResult prName nGoal excep = return $ case excep of
    -- this is supposed to distinguish "fd ... vanished"
    -- errors from other exceptions
    Exception.IOException e ->
        (ATPState.ATPError ("Internal error communicating with " ++
                            prName ++ ".\n"
                            ++ show e), emptyCfg)
    Exception.AsyncException Exception.ThreadKilled ->
        (ATPState.ATPBatchStopped, emptyCfg)
    _ -> (ATPState.ATPError ("Error running " ++ prName ++ ".\n"
                             ++ show excep),
          emptyCfg)
  where
    emptyCfg = ATPState.emptyConfig prName (AS_Anno.senAttr nGoal)
               emptyProofTree

{- |
  Returns the time limit from GenericConfig if available. Otherwise
  guiDefaultTimeLimit is returned.
-}
configTimeLimit :: ATPState.GenericConfig ProofTree
                -> Int
configTimeLimit cfg =
    maybe (guiDefaultTimeLimit) id $ ATPState.timeLimit cfg

{- |
  Creates a list of all options the zChaff prover runs with.
  Only Option is the timelimit
-}
createZchaffOptions :: ATPState.GenericConfig ProofTree -> [String]
createZchaffOptions cfg =
    [(show $ configTimeLimit cfg)]
