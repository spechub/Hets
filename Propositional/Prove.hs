{- |
Module      :  $Header$
Description :  Provers for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

This is the connection of the SAT-Solver minisat to Hets
-}

module Propositional.Prove
    ( zchaffProver                   -- the zChaff II Prover
    , propConsChecker
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
import Common.Utils
import qualified Common.AS_Annotation as AS_Anno
import qualified Common.OrderedMap as OMap
import qualified Common.Result as Result

import Control.Monad (when)
import qualified Control.Concurrent as Concurrent

import Data.List
import Data.Maybe
import Data.Time (TimeOfDay, timeToTimeOfDay, midnight)

import System.Directory
import System.Process
import System.Exit

-- * Prover implementation

zchaffHelpText :: String
zchaffHelpText = "Zchaff is a very fast SAT-Solver \n" ++
                 "No additional Options are available" ++
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
zchaffProver = LP.mkAutomaticProver zchaffS top zchaffProveGUI
  zchaffProveCMDLautomaticBatch

{- |
   The Consistency Cheker.
-}
propConsChecker :: LP.ConsChecker Sig.Sign AS_BASIC.FORMULA PropSL
                                  PMorphism.Morphism ProofTree
propConsChecker = LP.mkConsChecker zchaffS top consCheck

consCheck :: String -> LP.TacticScript
   -> LP.TheoryMorphism Sig.Sign AS_BASIC.FORMULA PMorphism.Morphism ProofTree
   -> [LP.FreeDefMorphism AS_BASIC.FORMULA PMorphism.Morphism]
    -- ^ free definitions
   -> IO (LP.CCStatus ProofTree)
consCheck thName _ tm _ =
    case LP.tTarget tm of
      LP.Theory sig nSens -> do
            let axioms = getAxioms $ snd $ unzip $ OMap.toList nSens
                thName_clean = basename thName ++ "_cc.zchaff.dimacs"
            dimacsOutput <- PC.showDIMACSProblem (thName ++ "_cc")
                             sig axioms Nothing
            tmpFile <- getTempFile dimacsOutput thName_clean
            (exitCode, resultHf, _) <-
              readProcessWithExitCode zchaffS [tmpFile] ""
            return $ if exitCode /= ExitSuccess then LP.CCStatus
                   (ProofTree $ "error by call zchaff " ++ thName)
                   midnight Nothing
               else LP.CCStatus (ProofTree resultHf) midnight
                       $ searchResult resultHf
    where
        getAxioms :: [LP.SenStatus AS_BASIC.FORMULA (LP.ProofStatus ProofTree)]
                  -> [AS_Anno.Named AS_BASIC.FORMULA]
        getAxioms f = map (AS_Anno.makeNamed "consistency" . AS_Anno.sentence)
          $ filter AS_Anno.isAxiom f
        searchResult :: String -> Maybe Bool
        searchResult hf = let ls = lines hf in
          if any (isInfixOf reUNSAT) ls then Just False else
          if any (isInfixOf reSAT) ls then Just True
          else Nothing

-- ** GUI

{- |
  Invokes the generic prover GUI.
-}
zchaffProveGUI :: String -- ^ theory name
          -> LP.Theory Sig.Sign AS_BASIC.FORMULA ProofTree
          -> [LP.FreeDefMorphism AS_BASIC.FORMULA PMorphism.Morphism]
          -- ^ free definitions
          -> IO [LP.ProofStatus ProofTree] -- ^ proof status for each goal
zchaffProveGUI thName th freedefs =
    genericATPgui (atpFun thName) True (LP.proverName zchaffProver) thName th
                  freedefs emptyProofTree
{- |
  Parses a given default tactic script into a
  'Interfaces.GenericATPState.ATPTacticScript' if possible.
-}
parseZchaffTacticScript :: LP.TacticScript -> ATPTacticScript
parseZchaffTacticScript = parseTacticScript batchTimeLimit []

-- ** command line function

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the zchaff prover.
  zchaff specific functions are omitted by data type ATPFunctions.
-}
zchaffProveCMDLautomaticBatch ::
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
        -> IO (Concurrent.ThreadId, Concurrent.MVar ())
           {- ^ fst: identifier of the batch thread for killing it
           snd: MVar to wait for the end of the thread -}
zchaffProveCMDLautomaticBatch inclProvedThs saveProblem_batch resultMVar
                        thName defTS th freedefs =
    genericCMDLautomaticBatch (atpFun thName) inclProvedThs saveProblem_batch
        resultMVar (LP.proverName zchaffProver) thName
        (parseZchaffTacticScript defTS) th freedefs emptyProofTree

{- |
  Record for prover specific functions. This is used by both GUI and command
  line interface.
-}
atpFun :: String            -- Theory name
  -> ATPFunctions Sig.Sign AS_BASIC.FORMULA PMorphism.Morphism ProofTree
     PState.PropProverState
atpFun thName = ATPFunctions
                { initialProverState = PState.propProverState
                , goalOutput = Cons.goalDIMACSProblem thName
                , atpTransSenName = PState.transSenName
                , atpInsertSentence = PState.insertSentence
                , proverHelpText = zchaffHelpText
                , runProver = runZchaff
                , batchTimeEnv = "HETS_ZCHAFF_BATCH_TIME_LIMIT"
                , fileExtensions = FileExtensions
                    { problemOutput = ".dimacs"
                    , proverOutput = ".zchaff"
                    , theoryConfiguration = ".czchaff"}
                , createProverOptions = createZchaffOptions }

{- |
  Runs zchaff. zchaff is assumed to reside in PATH.
-}

runZchaff :: PState.PropProverState
           {- logical part containing the input Sign and
           axioms and possibly goals that have been proved
           earlier as additional axioms -}
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
runZchaff pState cfg saveDIMACS thName nGoal = do
      prob <- Cons.goalDIMACSProblem thName pState nGoal []
      let thName_clean =
              basename thName ++ '_' : AS_Anno.senAttr nGoal ++ ".dimacs"
      when saveDIMACS (writeFile thName_clean prob)
      zFileName <- getTempFile prob thName_clean
      (_, zchaffOut, _) <- readProcessWithExitCode zchaffS
        (zFileName : createZchaffOptions cfg) ""
      (res, usedAxs, tUsed) <- analyzeZchaff zchaffOut pState
      let defaultProofStatus =
                      (LP.openProofStatus (AS_Anno.senAttr nGoal) zchaffS
                                        emptyProofTree)
                      {LP.tacticScript = LP.TacticScript $ show
                            ATPTacticScript
                             { tsTimeLimit = configTimeLimit cfg
                             , tsExtraOpts = []} }
          (err, retval) = case res of
                      Right p -> (ATPSuccess,
                        defaultProofStatus
                                {LP.goalStatus = p
                                , LP.usedAxioms = filter
                                    (/= AS_Anno.senAttr nGoal) usedAxs
                                , LP.proofTree = ProofTree zchaffOut })
                      Left a -> (a, defaultProofStatus)
      catch (removeFile zFileName) (const $ return ())
      return (err, cfg
              { proofStatus = retval
              , resultOutput = [zchaffOut]
              , timeUsed = tUsed })

-- | analysis of output
analyzeZchaff :: String -> PState.PropProverState
  -> IO (Either ATPRetval LP.GoalStatus, [String], TimeOfDay)
analyzeZchaff str' pState =
    let unsat = isInfixOf reUNSAT str'
        sat = isInfixOf reSAT str'
        timeLine = fromMaybe "0" $ stripPrefix reTIME str'
        timeout = isInfixOf reEndto str' || isInfixOf reEndmo str'
        time = calculateTime timeLine
        usedAx = map AS_Anno.senAttr $ PState.initialAxioms pState
    in return (case () of
         _ | timeout -> Left ATPTLimitExceeded
         _ | sat && not unsat -> Right LP.Disproved
         _ | not sat && unsat -> Right $ LP.Proved True
         _ -> Left $ ATPError "Internal error.", usedAx, time)

-- | Calculated the time need for the proof in seconds
calculateTime :: String -> TimeOfDay
calculateTime timeLine =
    timeToTimeOfDay $ realToFrac (fromMaybe
         (error $ "calculateTime " ++ timeLine) $ readMaybe timeLine
             :: Double)

reUNSAT :: String
reUNSAT = "RESULT:\tUNSAT"
reSAT :: String
reSAT = "RESULT:\tSAT"
reTIME :: String
reTIME = "Total Run Time"

reEndto :: String
reEndto = "TIME OUT"
reEndmo :: String
reEndmo = "MEM OUT"

{- |
  Creates a list of all options the zChaff prover runs with.
  Only Option is the timelimit
-}
createZchaffOptions :: GenericConfig ProofTree -> [String]
createZchaffOptions cfg =
    [show $ configTimeLimit cfg]
