{- |
Module      :  ./TPTP/ConsChecker.hs
Description :  Interface to consistency checkers
Copyright   :  (c) (c) Otto-von-Guericke University of Magdeburg, 2020
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  mscodescu@gmail.com
Stability   :  provisional
Portability :  needs POSIX

-}

module TPTP.ConsChecker
    where

import Logic.Prover

import Common.ProofTree
import qualified Common.Result as Result
import Common.AS_Annotation as AS_Anno
import Common.SZSOntology
import Common.Timing
import Common.Utils

import TPTP.Sign
import TPTP.Morphism
import TPTP.Translate
import TPTP.Prover.ProverState
import TPTP.Sublogic

import GUI.GenericATP
import Proofs.BatchProcessing
import Interfaces.GenericATPState

import System.Directory

import Control.Monad (when)
import qualified Control.Concurrent as Concurrent

import Data.Char
import Data.List
import Data.Maybe

import Data.Time.LocalTime (TimeOfDay, midnight)
import Data.Time (timeToTimeOfDay)
import Data.Time.Clock (secondsToDiffTime)
import qualified SoftFOL.ProveDarwin as Darwin

extras :: Darwin.ProverBinary -> Bool -> String -> String
extras b cons tl = let
  tOut = " -to " ++ tl
  darOpt = "-pc false"
  fdOpt = darOpt ++ (if cons then " -pmtptp true" else "") ++ " -fd true"
  in case b of
    Darwin.EProver -> Darwin.eproverOpts (if cons then "-s" else "") ++ tl
    Darwin.Leo -> "-t " ++ tl
    Darwin.Darwin -> fdOpt ++ tOut
    Darwin.DarwinFD -> fdOpt ++ tOut
    Darwin.EDarwin -> fdOpt ++ " -eq Axioms" ++ tOut
    Darwin.IProver -> "--time_out_real " ++ tl ++ " --sat_mode true"

{- | Runs the Darwin service. The tactic script only contains a string for the
  time limit. -}
consCheck
  :: Darwin.ProverBinary
  -> String
  -> TacticScript
  -> TheoryMorphism Sign Sentence Morphism ProofTree
  -> [FreeDefMorphism Sentence Morphism] -- ^ freeness constraints
  -> IO (CCStatus ProofTree)
consCheck b thName (TacticScript tl) tm freedefs = case tTarget tm of
    Theory sig nSens -> do
        let proverStateI = tptpProverState sig (toNamedList nSens) freedefs
        prob <- showTPTPProblemM thName proverStateI []
        (exitCode, out, tUsed) <-
          Darwin.runDarwinProcess (Darwin.darwinExe b) False (extras b True tl) thName prob
        let outState = CCStatus
               { ccResult = Just True
               , ccProofTree = ProofTree $ unlines $ exitCode : out
               , ccUsedTime = timeToTimeOfDay $ secondsToDiffTime
                            $ toInteger tUsed }
        return $ if szsProved exitCode then outState else
                    outState
                    { ccResult = if szsDisproved exitCode then Just False
                                 else Nothing }

darwinConsChecker
  :: Darwin.ProverBinary -> ConsChecker Sign Sentence Sublogic Morphism ProofTree
darwinConsChecker b =
  (mkUsableConsChecker (Darwin.darwinExe b) (Darwin.proverBinary b) FOF $ consCheck b)
  { ccNeedsTimer = False }
