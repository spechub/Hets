{- |
Module      :  $Header$
Description :  Interface for the SPASS theorem prover using Vampire.
Copyright   :  (c) Rene Wagner, Klaus Lüttich, Rainer Grabbe, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rainer25@tzi.de
Stability   :  provisional
Portability :  needs POSIX

Interface for the Vampire service, uses GUI.GenericATP.
See <http://spass.mpi-sb.mpg.de/> for details on SPASS.

-}

module SPASS.ProveVampire (vampire,vampireGUI) where

import Logic.Prover

import SPASS.Sign
import SPASS.ProveHelp
import SPASS.Translate
import SPASS.MathServParsing
import SPASS.ProverState

import qualified Common.AS_Annotation as AS_Anno

import Data.List
import Data.Maybe

import HTk

import GUI.GenericATP
import GUI.GenericATPState

-- * Prover implementation

{- |
  The Prover implementation. First runs the batch prover (with graphical
  feedback), then starts the GUI prover.
-}
vampire :: Prover Sign Sentence ()
vampire = 
  Prover { prover_name = "Vampire",
           prover_sublogic = "SoftFOL",
           prove = vampireGUI
         }


-- * Main GUI

{- |
  Invokes the generic prover GUI. SPASS specific functions are omitted by
  data type ATPFunctions.
-}
vampireGUI :: String -- ^ theory name
           -> Theory Sign Sentence ()
           -- ^ theory consisting of a SPASS.Sign.Sign
           --   and a list of Named SPASS.Sign.Sentence
           -> IO([Proof_status ()]) -- ^ proof status for each goal
vampireGUI thName th =
    genericATPgui atpFun True (prover_name vampire) thName th ()

    where
      atpFun = ATPFunctions
        { initialProverState = spassProverState,
          atpTransSenName = transSenName,
          atpInsertSentence = insertSentenceGen,
          goalOutput = showTPTPProblem thName,
          proverHelpText = spassHelpText,
          batchTimeEnv = "HETS_SPASS_BATCH_TIME_LIMIT",
          fileExtensions = FileExtensions{problemOutput = ".tptp",
                                          proverOutput = ".spass",
                                          theoryConfiguration = ".spcf"},
          runProver = runVampire}

{- |
  Runs the Vampire service.
-}
runVampire :: SPASSProverState
           -- ^ logical part containing the input Sign and axioms and possibly
           --   goals that have been proved earlier as additional axioms
           -> GenericConfig () -- ^ configuration to use
           -> Bool -- ^ True means save TPTP file
           -> String -- ^ name of the theory in the DevGraph
           -> AS_Anno.Named SPTerm -- ^ goal to prove
           -> IO (ATPRetval, GenericConfig ())
           -- ^ (retval, configuration with proof status and complete output)
runVampire sps cfg saveTPTP thName nGoal = do
    putStrLn ("running MathServ VampireService...")
    prob <- showTPTPProblem thName sps nGoal
    when saveTPTP
        (writeFile (thName++'_':AS_Anno.senName nGoal++".tptp") prob)
    mathServOut <- callMathServ
        MathServCall{ mathServService = VampireService,
                      mathServOperation = TPTPProblem,
                      problem = prob,
                      proverTimeLimit = tLimit,
                      extraOptions = Just $ unwords $ extraOpts cfg}
    parseMathServOut mathServOut cfg nGoal (prover_name vampire)
    where
      tLimit = maybe (guiDefaultTimeLimit) id $ timeLimit cfg
