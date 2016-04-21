{- |
Module      :  ./OWL2/ProveFact.hs
Copyright   :  (c) Domink Luecke, Uni Bremen 2009-2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable

Fact++ prover for OWL
-}

module OWL2.ProveFact (factProver, factConsChecker) where
import Data.List (intercalate) -- DEBUG

import Logic.Prover

import OWL2.MS
import OWL2.Morphism
import OWL2.Sign
import OWL2.ProfilesAndSublogics
import OWL2.ProverState

import GUI.GenericATP
import Interfaces.GenericATPState

import Proofs.BatchProcessing

import Common.AS_Annotation
import Common.ProofTree
import qualified Common.Result as Result
import Common.ProverTools
import Common.Utils
import Common.Timing

import Data.Time (TimeOfDay, midnight)

import System.Exit
import System.Environment
import System.Directory
import System.FilePath

import Control.Concurrent
import Control.Monad (when)

import Data.Maybe

{- |
  The Prover implementation. First runs the batch prover (with graphical
  feedback), then starts the GUI prover.
-}
factProver :: Prover Sign Axiom OWLMorphism ProfSub ProofTree
factProver = (mkAutomaticProver "java" "Fact" topS factGUI
  factCMDLautomaticBatch)
  { proverUsable = checkOWLjar factProverJarS }

factProverJarS :: String
factProverJarS = "OWLFactProver.jar"

factJarS :: String
factJarS = "OWLFact.jar"

{- |
  Invokes the generic prover GUI.
-}
factGUI :: String -- ^ theory name
          -> Theory Sign Axiom ProofTree
          -> [FreeDefMorphism Axiom OWLMorphism] -- ^ freeness constraints
          -> IO [ProofStatus ProofTree] -- ^ proof status for each goal
factGUI thName th freedefs =
  genericATPgui (atpFun thName) True (proverName factProver) thName th
                freedefs emptyProofTree

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the Fact prover.
  Pellet specific functions are omitted by data type ATPFunctions.
-}
factCMDLautomaticBatch ::
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
factCMDLautomaticBatch inclProvedThs saveProblem_batch resultMVar
                         thName defTS th freedefs =
  genericCMDLautomaticBatch (atpFun thName) inclProvedThs saveProblem_batch
    resultMVar (proverName factProver) thName
    (parseTacticScript batchTimeLimit [] defTS) th freedefs emptyProofTree

{- |
  The Cons-Checker implementation.
-}
factConsChecker :: ConsChecker Sign Axiom ProfSub OWLMorphism ProofTree
factConsChecker = (mkConsChecker "Fact" topS consCheck)
  { ccUsable = checkOWLjar factJarS }

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
  , proverHelpText = "Fact++"
  , batchTimeEnv = "HETS_FACT_BATCH_TIME_LIMIT"
  , fileExtensions = FileExtensions { problemOutput = ".owl"  -- owl-hets
                                    , proverOutput = ".fact"
                                    , theoryConfiguration = ".pconf" }
  , runProver = runFact
  , createProverOptions = extraOpts }

{- |
  Runs the Fact++ consistency checker.
-}
consCheck :: String
          -> TacticScript
          -> TheoryMorphism Sign Axiom OWLMorphism ProofTree
          -> [FreeDefMorphism Axiom OWLMorphism] -- ^ freeness constraints
          -> IO (CCStatus ProofTree)
consCheck thName (TacticScript tl) tm freedefs = case tTarget tm of
  Theory sig nSens ->
   do
    let saveOWL = False
        proverStateI = owlProverState sig (toNamedList nSens) freedefs
        problemS = showOWLProblemS proverStateI
        tmpFileName = basename thName ++ ".owl"
        pStatus out tUsed = CCStatus
          { ccResult = Nothing
          , ccProofTree = ProofTree $ out ++ "\n\n" ++ problemS
          , ccUsedTime = tUsed }
    when saveOWL (writeFile tmpFileName problemS)
    res <- runTimedFact tmpFileName problemS Nothing
      $ fromMaybe maxBound $ readMaybe tl
    return $ case res of
      Just (b, ex_code, out, t_u) -> let pStat = pStatus out t_u in if b then
        case ex_code of
          ExitFailure 10 -> pStat { ccResult = Just True }
          ExitFailure 20 -> pStat { ccResult = Just False}
          _ -> pStat
        else pStat
      Nothing -> pStatus "Timeout" midnight

runTimedFact :: FilePath -- ^ basename of problem file
  -> String              -- ^ problem content
  -> Maybe String        -- ^ entail content
  -> Int                 -- ^ time limit in seconds
  -> IO (Maybe (Bool, ExitCode, String, TimeOfDay))
runTimedFact tmpFileName prob mEnt tLimit = do
  let hasEnt = isJust mEnt
      jar = if hasEnt then factProverJarS else factJarS
  (progTh, toolPath) <- check4HetsOWLjar jar
  (_, arch, _) <- executeProcess "uname" ["-m"] ""
  if progTh then
        withinDirectory toolPath $ do
          mLibraryPath <- fmap (lookup "LD_LIBRARY_PATH") getEnvironment
          let libraryPath = fromMaybe ("lib/native/" ++ trim arch) mLibraryPath
          timeTmpFile <- getTempFile prob tmpFileName
          let entailsFile = timeTmpFile ++ ".entail.owl"
              jargs = ["-Djava.library.path=" ++ libraryPath
                        | isJust mLibraryPath ]
                 ++ ["-jar", jar, "file://" ++ timeTmpFile]
                 ++ ["file://" ++ entailsFile | hasEnt ]
          case mEnt of
            Just entail -> writeFile entailsFile entail
            _ -> return ()
          putStrLn $ "" -- DEBUG
          putStrLn $ "jargs: " ++ (intercalate " " jargs) -- DEBUG
          putStrLn $ "mLibraryPath: " ++ show mLibraryPath -- DEBUG
          executeProcess "cp" [timeTmpFile, "/tmp/timeTmpFile.owl"] "" -- DEBUG
          executeProcess "cp" [entailsFile, "/tmp/entailsFile.owl"] "" -- DEBUG
          t_start <- getHetsTime
          mExit <- timeoutCommand tLimit "java" jargs
          putStrLn $ (\ (Just (ex, out, err)) -> "exitCode: " ++ show ex) mExit -- DEBUG
          putStrLn $ (\ (Just (ex, out, err)) -> "out: " ++ out) mExit -- DEBUG
          putStrLn $ (\ (Just (ex, out, err)) -> "err: " ++ err) mExit -- DEBUG
          putStrLn $ "" -- DEBUG
          putStrLn $ "" -- DEBUG
          t_end <- getHetsTime
          removeFile timeTmpFile
          when hasEnt $ removeFile entailsFile
          return $ fmap (computeResult t_start t_end) mExit
    else return $ Just (False, ExitSuccess, jar ++ " not found.", midnight)
  where
    computeResult :: HetsTime
                  -> HetsTime
                  -> (ExitCode, String, String)
                  -> (Bool, ExitCode, String, TimeOfDay)
    computeResult t_start t_end (exitCode, out, err) = case exitCode of
      ExitSuccess -> (True, exitCode, out ++ err, diffHetsTime t_end t_start)
      _ -> (False, exitCode, "Java Error:\n" ++ err, diffHetsTime t_end t_start)

{- |
   Invocation of the Fact Prover.
-}
runFact :: ProverState
          {- ^ logical part containing the input Sign and axioms and possibly
          goals that have been proved earlier as additional axioms -}
          -> GenericConfig ProofTree -- ^ configuration to use
          -> Bool -- ^ True means save TPTP file
          -> String -- ^ name of the theory in the DevGraph
          -> Named Axiom -- ^ goal to prove
          -> IO (ATPRetval, GenericConfig ProofTree)
          -- ^ (retval, configuration with proof status and complete output)
runFact sps cfg saveFact thName nGoal = do
      let prob = showOWLProblemS sps
          entail = showOWLProblemS
            sps { initialState = [ nGoal {isAxiom = True } ] }
      when saveFact $ do
        writeFile tmpFileName prob
        writeFile (tmpFileName ++ ".entail.owl") entail
      mExit <- runTimedFact tmpFileName prob (Just entail) tLimit
      ((err, retval), output, tUsed) <- case mExit of
            Just (b, ex, output, t_u) -> if b then do
              let outp = lines output
              return (proofStat ex outp t_u, outp, t_u)
              else return ((ATPError output, defaultProofStatus), [], t_u)
            Nothing -> return
              ( (ATPTLimitExceeded, defaultProofStatus)
              , [], midnight)
      return (err, cfg
            { proofStatus = retval
            , resultOutput = output
            , timeUsed = tUsed
            })
  where
    tLimit = fromMaybe 800 $ timeLimit cfg
    goalSuffix = '_' : senAttr nGoal
    tmpFileName = basename thName ++ goalSuffix ++ ".owl"
    proofStat exitCode out tUsed = case exitCode of
      ExitFailure 10 -> (ATPSuccess, (provedStatus tUsed)
                       { usedAxioms = map senAttr $ initialState sps })
      ExitFailure 20 -> (ATPSuccess, disProvedStatus)
      ExitFailure _ -> ( ATPError (unlines ("Internal error." : out))
                       , defaultProofStatus)
      ExitSuccess -> ( ATPError (unlines ("Internal error." : out))
                       , defaultProofStatus)
    tScript = TacticScript $ show ATPTacticScript
                     { tsTimeLimit = configTimeLimit cfg
                     , tsExtraOpts = extraOpts cfg }
    defaultProofStatus =
      (openProofStatus (senAttr nGoal) (proverName factProver) emptyProofTree)
        { tacticScript = tScript }
    disProvedStatus = defaultProofStatus {goalStatus = Disproved}
    provedStatus ut =
      defaultProofStatus { goalStatus = Proved True
                         , usedTime = ut
                         , tacticScript = tScript }
