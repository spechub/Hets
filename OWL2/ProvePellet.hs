{- |
Module      :  ./OWL2/ProvePellet.hs
Description :  Interface to the OWL Ontology prover via Pellett.
Copyright   :  (c) Heng Jiang, Uni Bremen 2004-2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  needs POSIX

Interface for the Pellet service, uses GUI.GenericATP.
See <http://www.w3.org/2004/OWL/> for details on OWL, and
<http://pellet.owldl.com/> for Pellet (version 2.0.0-rc6)
-}

module OWL2.ProvePellet
  ( runTimedPellet
  , pelletJar
  , pelletEnv
  , pelletProver
  , pelletConsChecker
  ) where

import Logic.Prover

import OWL2.Morphism
import OWL2.Sign
import OWL2.Profiles
import OWL2.Sublogic
import OWL2.ProfilesAndSublogics
import OWL2.ProverState
import OWL2.MS

import GUI.GenericATP
import Interfaces.GenericATPState

import Proofs.BatchProcessing

import Common.AS_Annotation
import Common.ProofTree
import Common.Result as Result
import Common.ProverTools
import Common.Utils

import Data.Char (isDigit)
import Data.List (isPrefixOf)
import Data.Maybe
import Data.Time (timeToTimeOfDay)
import Data.Time.Clock (secondsToDiffTime)

import System.Directory

import Control.Monad (when)
import Control.Concurrent

pelletS :: String
pelletS = "Pellet"

pelletJar :: String
pelletJar = "lib/pellet-cli.jar"

pelletEnv :: String
pelletEnv = "PELLET_PATH"

pelletCheck :: IO (Maybe String)
pelletCheck = fmap
  (\ l ->
    if null l
    then Just $ pelletJar ++ " not found in $" ++ pelletEnv
    else Nothing)
  $ check4FileAux pelletJar pelletEnv

{- |
  The Prover implementation. First runs the batch prover (with graphical
  feedback), then starts the GUI prover.
-}
pelletProver :: Prover Sign Axiom OWLMorphism ProfSub ProofTree
pelletProver =
  (mkAutomaticProver "java" pelletS topS pelletGUI pelletCMDLautomaticBatch)
  { proverUsable = pelletCheck }

pelletConsChecker :: ConsChecker Sign Axiom ProfSub OWLMorphism ProofTree
pelletConsChecker = (mkConsChecker pelletS topS consCheck)
  { ccNeedsTimer = False
  , ccUsable = pelletCheck }

{- |
  Record for prover specific functions. This is used by both GUI and command
  line interface.
-}
atpFun :: String -- ^ theory name
       -> ATPFunctions Sign Axiom OWLMorphism ProofTree ProverState
atpFun _ = ATPFunctions
  { initialProverState = owlProverState
  , atpTransSenName = id   -- transSenName,
  , atpInsertSentence = insertOWLAxiom
  , goalOutput = \ a b _ -> showOWLProblem a b
  , proverHelpText = "http://clarkparsia.com/pellet/\n"
  , batchTimeEnv = "HETS_Pellet_BATCH_TIME_LIMIT"
  , fileExtensions = FileExtensions { problemOutput = ".owl"  -- owl-hets
                                    , proverOutput = ".pellet"
                                    , theoryConfiguration = ".pconf" }
  , runProver = runPellet
  , createProverOptions = extraOpts }

-- ** GUI

{- |
  Invokes the generic prover GUI.
-}
pelletGUI :: String -- ^ theory name
          -> Theory Sign Axiom ProofTree
          -> [FreeDefMorphism Axiom OWLMorphism] -- ^ freeness constraints
          -> IO [ProofStatus ProofTree] -- ^ proof status for each goal
pelletGUI thName th freedefs =
  genericATPgui (atpFun thName) True pelletS thName th
                freedefs emptyProofTree

-- ** command line function

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the Pellet prover via MathServe.
  Pellet specific functions are omitted by data type ATPFunctions.
-}
pelletCMDLautomaticBatch ::
           Bool -- ^ True means include proved theorems
        -> Bool -- ^ True means save problem file
        -> MVar (Result.Result [ProofStatus ProofTree])
           -- ^ used to store the result of the batch run
        -> String -- ^ theory name
        -> TacticScript -- ^ default tactic script
        -> Theory Sign Axiom ProofTree -- ^ theory
        -> [FreeDefMorphism Axiom OWLMorphism] -- ^ freeness constraints
        -> IO (ThreadId, MVar ())
        {- ^ fst: identifier of the batch thread for killing it
        snd: MVar to wait for the end of the thread -}
pelletCMDLautomaticBatch inclProvedThs saveProblem_batch resultMVar
                         thName defTS th freedefs =
  genericCMDLautomaticBatch (atpFun thName) inclProvedThs saveProblem_batch
    resultMVar pelletS thName
    (parseTacticScript batchTimeLimit [] defTS) th freedefs emptyProofTree

-- * Main prover functions

{- |
  Runs the Pellet service.
-}
consCheck :: String
          -> TacticScript
          -> TheoryMorphism Sign Axiom OWLMorphism ProofTree
          -> [FreeDefMorphism Axiom OWLMorphism] -- ^ freeness constraints
          -> IO (CCStatus ProofTree)
consCheck thName (TacticScript tl) tm freedefs = case tTarget tm of
  Theory sig nSens -> do
    let proverStateI = owlProverState sig (toNamedList nSens) freedefs
        prob = showOWLProblemS proverStateI
        pStatus out tUsed = CCStatus
          { ccResult = Nothing
          , ccProofTree = ProofTree $ unlines out ++ "\n\n" ++ prob
          , ccUsedTime = timeToTimeOfDay $ secondsToDiffTime $ toInteger tUsed }
        tLim = readMaybe tl
    res <- runTimedPellet "consistency" (basename thName ++ ".owl") prob Nothing
      $ fromMaybe maxBound $ readMaybe tl
    return $ case res of
      Nothing -> pStatus ["Timeout after " ++ tl ++ " seconds"]
                 (fromMaybe (0 :: Int) tLim)
      Just (progTh, outp, eOut) -> if progTh then
          let (_, exCode, out, tUsed) = analyseOutput outp eOut
          in (pStatus out tUsed) { ccResult = exCode }
        else pStatus ["Pellet not found"] (0 :: Int)

runTimedPellet :: String -- ^ pellet subcommand
  -> FilePath            -- ^ basename of problem file
  -> String              -- ^ problem content
  -> Maybe String        -- ^ entail content
  -> Int                 -- ^ time limit in seconds
  -> IO (Maybe (Bool, String, String)) -- ^ timeout or (success, stdout, stderr)
runTimedPellet opts tmpFileName prob entail secs = do
  (progTh, pPath) <- check4jarFile pelletEnv pelletJar
  if progTh then withinDirectory pPath $ do
      timeTmpFile <- getTempFile prob tmpFileName
      let entFile = timeTmpFile ++ ".entail.owl"
          doEntail = isJust entail
          args = "-Xmx512m" : "-jar" : pelletJar
           : (if doEntail then ["entail", "-e", entFile] else words opts)
           ++ ["file://" ++ timeTmpFile]
      case entail of
        Just c -> writeFile entFile c
        Nothing -> return ()
      mex <- timeoutCommand secs "java" args
      removeFile timeTmpFile
      when doEntail $ removeFile entFile
      return $ fmap (\ (_, outS, errS) -> (True, outS, errS)) mex
    else return $ Just (False, "", "")

runPellet :: ProverState
          {- ^ logical part containing the input Sign and axioms and possibly
          goals that have been proved earlier as additional axioms -}
          -> GenericConfig ProofTree -- ^ configuration to use
          -> Bool -- ^ True means save TPTP file
          -> String -- ^ name of the theory in the DevGraph
          -> Named Axiom -- ^ goal to prove
          -> IO (ATPRetval, GenericConfig ProofTree)
          -- ^ (retval, configuration with proof status and complete output)
runPellet sps cfg savePellet thName nGoal = do
  let simpleOptions = extraOpts cfg
      tLimit = fromMaybe 800 $ timeLimit cfg
      goalSuffix = '_' : senAttr nGoal
      tmpFileName = basename thName ++ goalSuffix ++ ".owl"
      tScript = TacticScript $ show ATPTacticScript
                     { tsTimeLimit = configTimeLimit cfg
                     , tsExtraOpts = simpleOptions }
      defaultProofStatus out =
        (openProofStatus (senAttr nGoal) pelletS $ ProofTree out)
        { tacticScript = tScript }
      prob = showOWLProblemS sps
      entail = showOWLProblemS
                     sps { initialState = [ nGoal {isAxiom = True } ] }
  when savePellet $ do
        writeFile tmpFileName prob
        writeFile (tmpFileName ++ ".entail.owl") entail
  res <- runTimedPellet "" tmpFileName prob (Just entail) tLimit
  ((err, retval), output, tUsed) <- return $ case res of
    Nothing ->
      ((ATPTLimitExceeded, defaultProofStatus "Timeout"), [], tLimit)
    Just (progTh, output, eOut) ->
      if progTh then
        let (atpr, exCode, outp, tUsed) = analyseOutput output eOut
            openStat = defaultProofStatus $ unlines outp
            disProvedStatus = openStat
               { goalStatus = Disproved
               , usedTime =
                   timeToTimeOfDay $ secondsToDiffTime $ toInteger tUsed }
            provedStatus = disProvedStatus
                  { goalStatus = Proved True
                  , usedAxioms = map senAttr $ initialState sps }
            proofStat = case exCode of
              Just True -> provedStatus
              Just False -> disProvedStatus
              _ -> openStat
        in ((atpr, proofStat), outp, tUsed)
      else
       ((ATPError "Could not find pellet prover. Is $PELLET_PATH set?"
       , defaultProofStatus ""), [], 0)
  return (err, cfg
    { proofStatus = retval
    , resultOutput = output
    , timeUsed = timeToTimeOfDay $ secondsToDiffTime $ toInteger tUsed
    })

analyseOutput :: String -> String -> (ATPRetval, Maybe Bool, [String], Int)
analyseOutput err outp =
  let ls = lines outp ++ lines err
      anaHelp (atp, exCode, to) line =
        case words line of
          "Consistent:" : v : _ -> case v of
              "Yes" -> (ATPSuccess, Just True, to)
              "No" -> (ATPSuccess, Just False, to)
              _ -> (atp, exCode, to)
          "All" : "axioms" : "are" : e : _ | isPrefixOf "entailed" e ->
            (ATPSuccess, Just True, to)
          ne : _ | isPrefixOf "Non-entailments" ne ->
            (ATPSuccess, Just False, to)
          "Usage:" : "java" : "Pellet" : _ -> (ATPError line, Nothing, to)
          "ERROR:" : _ -> (ATPError line, Nothing, to)
          tm : num : _ | isPrefixOf "Time" tm && all isDigit num ->
            (atp, exCode, read num)
          _ -> (atp, exCode, to)
      (atpr, st, tmo) = foldl anaHelp (ATPError "", Nothing, -1) ls
  in case atpr of
       ATPError s | null s -> (ATPError "unexpected pellet output", st, ls, tmo)
       _ -> (atpr, st, ls, tmo)
