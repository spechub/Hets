{- |
Module      :  ./TPTP/ConsChecker.hs
Description :  Interface to the theorem prover e-krhyper in CASC-mode.
Copyright   :  (c) Dominik Luecke, Uni Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  needs POSIX

Check out
http://www.uni-koblenz.de/~bpelzer/ekrhyper/
for details. For the ease of maintenance we are using e-krhyper in
its CASC-mode, aka tptp-input. It works for single input files and
fof-style.
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

extras :: String -> Bool -> String -> String
extras b cons tl = let
  tOut = " -to " ++ tl
  darOpt = "-pc false"
  fdOpt = darOpt ++ (if cons then " -pmtptp true" else "") ++ " -fd true"
  in case b of
    "eprover" -> Darwin.eproverOpts (if cons then "-s" else "") ++ tl
    "leo" -> "-t " ++ tl
    "darwin" -> fdOpt ++ tOut
    -- "DarwinFD" -> fdOpt ++ tOut
    "e-darwin" -> fdOpt ++ " -eq Axioms" ++ tOut
    "iproveropt" -> "--time_out_real " ++ tl ++ " --sat_mode true"

{- | Runs the Darwin service. The tactic script only contains a string for the
  time limit. -}
consCheck
  :: String
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
          Darwin.runDarwinProcess b False (extras b True tl) thName prob
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
  :: String -> ConsChecker Sign Sentence Sublogic Morphism ProofTree
darwinConsChecker binary =
  (mkUsableConsChecker binary binary FOF $ consCheck binary)
  { ccNeedsTimer = False }
