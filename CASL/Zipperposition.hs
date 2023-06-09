{- |
Module      :  ./CASL/Zipperposition.hs
Description :  Zipperposition prover for CASL
Copyright   :  (c) Tom Kranz 2022
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :
Stability   :  experimentatl
Portability :  non-portable (via GUI imports)

provides higher-order and first-order+induction prover for CASL

The FO+induction prover only works if all sort-generation constraints are
  introduced via free-datatype declarations. Higher-order mode can deal with
  anything by receiving any sort-generation constraints as second-order
  induction axioms.
  Currently limited by an inability to parse simultaneous (interdependent) data
  type declarations and annotations (e.g. axiom names).
-}
module CASL.Zipperposition (zipperpositionFreeFolProver, zipperpositionCFolProver) where

import CASL.Sublogic
import CASL.Sign
import CASL.Morphism
import CASL.AS_Basic_CASL
import CASL.ToTIP
import qualified TIP.AbsTIP as T
import TIP.Prover.Common
import TIP.Utils
import Logic.Prover
import Common.AS_Annotation
import Common.ProofTree
import qualified Common.Result as Result
import Interfaces.GenericATPState
import TPTP.Prover.ProofParser
import TPTP.Prover.Common (executeTheProver,atpRetValAndProofStatus')
import GUI.GenericATP
import Common.SZSOntology
import Control.Concurrent
import Data.List (foldl',break,stripPrefix)
import Data.Maybe (mapMaybe)
import Data.Time (timeToTimeOfDay,picosecondsToDiffTime)
import qualified Data.Set as Set
import qualified Data.IntMap.Strict as IM
import Text.Read (readMaybe)
import Proofs.BatchProcessing

data ZipperpositionMode = ZPMode
  { name :: String
  , sublogic :: CASL_Sublogics
  , mode :: String
  , options :: [String]
  }

zpFreeFOL :: ZipperpositionMode
zpFreeFOL = 
  ZPMode 
    "Zipperposition (FOL+Induction)"
    (fol { cons_features = SortGen False False OnlyFree })
    "fo-complete-basic"
    ["--induction"]
zpCFOL :: ZipperpositionMode
zpCFOL =
  ZPMode
    "Zipperposition (HOL)"
    cFol
    "best"
    []

zpQuirks :: TIPQuirks
zpQuirks = noTIPQuirks { noAnnotations = True, noPluralDatatype = True }

zipperpositionFreeFolProver :: Prover CASLSign CASLFORMULA CASLMor CASL_Sublogics ProofTree
zipperpositionFreeFolProver = zipperpositionProver zpFreeFOL
zipperpositionCFolProver :: Prover CASLSign CASLFORMULA CASLMor CASL_Sublogics ProofTree
zipperpositionCFolProver = zipperpositionProver zpCFOL

zipperpositionProver :: ZipperpositionMode -> Prover CASLSign CASLFORMULA CASLMor CASL_Sublogics ProofTree
zipperpositionProver md =
  (mkProverTemplate (name md) (sublogic md) $ zipperpositionGUI md)
    { proveCMDLautomaticBatch = Just $ zipperpositionCMDLautomaticBatch md }

atpFun :: ZipperpositionMode
  -> String
  -> ATPFunctions CASLSign CASLFORMULA CASLMor ProofTree [T.Decl]
atpFun md _thryName = ATPFunctions
    { initialProverState = \ sig s _ -> tipSign (sig, s) ++ map tipAxiom (filter isAxiom s),
      atpTransSenName = id,
      atpInsertSentence = \ thry s -> thry ++ [tipAxiom s],
      goalOutput = \ thry nGoal _ -> do
            let tipTheory = T.Start thry
            let (tipProblem,_) = generateProblem noTIPQuirks tipTheory $ Just $ tipAxiom nGoal
            let tipProblemString = printTIP tipProblem
            return tipProblemString,
      proverHelpText = "" ,
      batchTimeEnv = "HETS_ZIPPERPOSITION_BATCH_TIME_LIMIT",
      fileExtensions = FileExtensions {problemOutput = ".smt2",
                                      proverOutput = ".tptp",
                                      theoryConfiguration = ".none3"},
      runProver = runZipperposition md,
      createProverOptions = \cfg ->
        [ "--input=tip"
        , "--output=tptp"
        , "--timeout=" ++ show (configTimeLimit cfg)
        , "--mode=" ++ mode md
        ] ++ options md ++ extraOpts cfg }

zipperpositionCMDLautomaticBatch :: ZipperpositionMode
        -> Bool -- ^ True means include proved theorems
        -> Bool -- ^ True means save problem file
        -> MVar (Result.Result [ProofStatus ProofTree])
           -- ^ used to store the result of the batch run
        -> String -- ^ theory name
        -> TacticScript -- ^ default tactic script
        -> Theory CASLSign CASLFORMULA ProofTree {- ^ theory consisting of a
           signature and a list of named sentences -}
        -> [FreeDefMorphism CASLFORMULA CASLMor] -- ^ freeness constraints
        -> IO (ThreadId, MVar ())
           {- ^ fst: identifier of the batch thread for killing it
           snd: MVar to wait for the end of the thread -}
zipperpositionCMDLautomaticBatch md inclProvedThs saveProblem_batch resultMVar
                        thName defTS th freedefs =
    genericCMDLautomaticBatch (atpFun md thName) inclProvedThs saveProblem_batch
        resultMVar (name md) thName
        (parseTacticScript batchTimeLimit [] defTS) th freedefs emptyProofTree

zipperpositionGUI :: ZipperpositionMode
  -> String -- ^ theory name
  -> Theory CASLSign CASLFORMULA ProofTree
  {- ^ theory consisting of a signature
  and a list of named sentences -}
  -> [FreeDefMorphism CASLFORMULA CASLMor] -- ^ freeness constraints
  -> IO [ProofStatus ProofTree] -- ^ proof status for each goal
zipperpositionGUI md thName th freedefs =
  genericATPgui (atpFun md thName) True (name md) thName th freedefs emptyProofTree

runZipperposition :: ZipperpositionMode
  -> [T.Decl]
  {- ^ logical part containing the input Sign and axioms and possibly
  goals that have been proved earlier as additional axioms -}
  -> GenericConfig ProofTree -- ^ configuration to use
  -> Bool -- ^ True means save theory file
  -> String -- ^ name of the theory in the DevGraph
  -> Named CASLFORMULA -- ^ goal to prove
  -> IO (ATPRetval, GenericConfig ProofTree)
runZipperposition md state cfg saveFile thName nGoal = do
  (problemFileName,blame) <-
    prepareProverInput (T.Start state) cfg saveFile thName (tipAxiom nGoal) zpQuirks (name md)
  let allOptions = createProverOptions (atpFun md thName) cfg ++ [problemFileName]
  (_, out, wallTimeUsed) <-
    executeTheProver "zipperposition" allOptions
  let szsStatusLine = findSZS out
  let reportedTimeUsed = parseTimeUsed out
  let resultedTimeUsed =
        if reportedTimeUsed == -1
        then wallTimeUsed
        else timeToTimeOfDay $ picosecondsToDiffTime reportedTimeUsed
  let proofOut = filterProofLines out
  let allAxiomNames = Set.fromList $ mapMaybe getFormulaName state
  axiomsUsed <- if szsProved szsStatusLine || szsDisproved szsStatusLine
                then case axiomsFromProofObject proofOut of
                  (axiomNames, []) -> return $
                    mapMaybe (mapAxiomName allAxiomNames state blame) axiomNames
                  (_, errs) -> do
                    putStrLn $ unlines errs
                    return $ Set.toList allAxiomNames
                else return $ Set.toList allAxiomNames
  let proofGraph = if szsProved szsStatusLine || szsDisproved szsStatusLine
                then graphFromProofObject proofOut
                else proofTree (proofStatus cfg)
  let (atpRetval, resultedProofStatus) =
        atpRetValAndProofStatus' cfg (senAttr nGoal)
          resultedTimeUsed axiomsUsed
          szsStatusLine (name md)
  return (atpRetval, cfg { proofStatus = resultedProofStatus { proofTree = proofGraph }
                         , resultOutput = out
                         , timeUsed = resultedTimeUsed })

parseTimeUsed :: [String] -> Integer
parseTimeUsed = fst . foldl' checkLine (-1, False)
  where
    checkLine :: (Integer, Bool) -> String -> (Integer, Bool)
    checkLine unchanged@(_time, found) line
      | found
      = unchanged
      | ["%", "done", _iterations, "iterations", "in", secs] <- words line
      , (sec, msecs) <- break (=='.') secs
      , Just s <- readMaybe sec
      , '.' : msec <- take 4 msecs
      , Just ms <- readMaybe msec
      = (s * 10^(12 :: Integer) + ms * 10^(9 :: Integer), True)
      | otherwise
      = unchanged

mapAxiomName :: Set.Set String -> [T.Decl] -> IM.IntMap Int -> String -> Maybe String
mapAxiomName allAx thry blame ax
  | ax `Set.member` allAx
  = Just ax
  | Just n <- stripPrefix "zf_stmt_" ax
  , Just lineN <- readMaybe n
  , Just originalLineN <- IM.lookup lineN blame
  , length thry > originalLineN
  = getFormulaName (thry !! lineN)
  | otherwise
  = Nothing
