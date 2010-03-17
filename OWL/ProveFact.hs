{- |
Module      :  $Header$
Copyright   :  (c) Domink Luecke, Uni Bremen 2009-2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable

Fact++ prover for OWL
-}

module OWL.ProveFact where

import Logic.Prover

import OWL.AS
import OWL.Morphism
import OWL.Sign
import OWL.Print
import OWL.Sublogic

import GUI.GenericATP()
import Interfaces.GenericATPState()
import GUI.Utils ()

import Proofs.BatchProcessing()

import Common.AS_Annotation
import Common.DefaultMorphism()
import Common.ProofTree
import Common.Result()
import Common.Utils

import Data.List ()
import Data.Time (timeToTimeOfDay)
import Data.Time.Clock (UTCTime(..), secondsToDiffTime, getCurrentTime)
import System.Posix.Time

import qualified Control.Concurrent()

import System.Exit
import System.IO
import System.Process
import System.Directory

import Control.Monad (when)
import Control.Concurrent.MVar()

data FactProverState = FactProverState
                           { ontologySign :: Sign
                           , initialState :: [Named Axiom]
                           } deriving (Show)

data FactProblem = FactProblem
                       { identifier :: String
                       -- , description :: Description
                       , problemProverState :: FactProverState
                       -- , settings :: [PelletSetting]
                       } deriving (Show)

-- * Prover implementation
factProverState :: Sign
                  -> [Named Axiom]
                  -> [FreeDefMorphism Axiom OWLMorphism]
                  -- ^ freeness constraints
                  -> FactProverState
factProverState sig oSens _ = FactProverState
  { ontologySign = sig
  , initialState = filter isAxiom oSens }
{- |
  The Cons-Checker implementation.
-}
factConsChecker :: ConsChecker Sign Axiom OWLSub OWLMorphism ProofTree
factConsChecker = mkConsChecker "Fact" sl_top consCheck

-- * Main prover functions
{- |
  Runs the Pellet service.
-}

getEnvSec :: String -> IO String
getEnvSec s = getEnvDef s ""

{- |
  Runs the Fact++ consistency checker.
-}
consCheck :: String
          -> TacticScript
          -> TheoryMorphism Sign Axiom OWLMorphism ProofTree
          -> [FreeDefMorphism Axiom OWLMorphism] -- ^ freeness constraints
          -> IO (CCStatus ProofTree)
consCheck thName _ tm freedefs = case tTarget tm of
  Theory sig nSens ->
   do
    let saveOWL = False
        proverStateI = factProverState sig (toNamedList nSens) freedefs
        problemS     = showOWLProblemS thName proverStateI []
        saveFileName  = reverse $ fst $ span (/='/') $ reverse thName
        tmpFileName   = saveFileName
        pStatus out tUsed = CCStatus
          { ccResult = Nothing
          , ccProofTree = ProofTree $ out ++ "\n\n" ++ problemS
          , ccUsedTime = timeToTimeOfDay $ secondsToDiffTime $ tUsed }
    when saveOWL (writeFile (saveFileName ++".owl") problemS)
    t <- getCurrentTime
    tempDir <- getTemporaryDirectory
    pPath <- getEnvSec "HETS_OWL_TOOLS"
    setCurrentDirectory pPath
    let timeTmpFile = tempDir ++ "/" ++ tmpFileName ++ show (utctDay t)
                                                 ++ "-" ++ show (utctDayTime t) ++ ".owl"
        tmpURI = "file://" ++ timeTmpFile
        command = "java -Djava.library.path=lib/native/`uname -m` -jar " ++ pPath ++ "/OWLFact.jar " ++ tmpURI
    writeFile timeTmpFile problemS
    t_start <- epochTime
    (_, outh, errh, proch) <- runInteractiveCommand command
    ex_code <- waitForProcess proch
    t_end <- epochTime
    let t_u = round (realToFrac (t_end - t_start) :: Double)
    outp <- hGetContents outh
    eOut <- hGetContents errh
    removeFile timeTmpFile
    let cRes = case ex_code of
                 ExitFailure 10 -> (pStatus (outp ++ eOut) t_u) { ccResult = Just True }
                 ExitFailure 20 -> (pStatus (outp ++ eOut) t_u) { ccResult = Just False}
                 _              -> (pStatus (outp ++ eOut) t_u) { ccResult = Nothing}
    return $ cRes

showOWLProblemS :: String -- ^ theory name
                -> FactProverState -- ^ prover state containing
                                     -- initial logical part
                -> [String] -- ^ extra options
                -> String -- ^ formatted output of the goal
showOWLProblemS thName pst _ =
    let namedSens = initialState $ problemProverState
                    $ genFactProblemS thName pst Nothing
        sign      = ontologySign $ problemProverState
                    $ genFactProblemS thName pst Nothing
    in show $ printOWLBasicTheory (sign, filter isAxiom namedSens)

genFactProblemS :: String
                  -> FactProverState
                  -> Maybe (Named Axiom)
                  -> FactProblem
genFactProblemS thName pps m_nGoal = FactProblem
  { identifier = thName
  , problemProverState =
      pps { initialState = initialState pps ++ maybe [] (:[]) m_nGoal } }
