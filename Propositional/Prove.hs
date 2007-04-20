{- |
Module      :  $Header$
Description :  Provers for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@tzi.de
Stability   :  experimental
Portability :  portable

This is the connection of the SAT-Solver minisat to Hets
-}

module Propositional.Prove
    where

import qualified Logic.Prover as LP
import qualified Propositional.Sign as Sig
import qualified Propositional.AS_BASIC_Propositional as AS_BASIC
import qualified Propositional.ProverState as PState
import qualified GUI.GenericATPState as ATPState
import qualified Propositional.Conversions as Cons
import qualified Common.AS_Annotation as AS_Anno

import qualified Control.Exception as Exception

import Data.Maybe

import System

import ChildProcess
import ProcessClasses

import HTk

import GUI.GenericATP

-- * Prover implementation

miniHelpText :: String
miniHelpText = "Minisat is a very fast SAT-Solver \
               \ no additional Options are available \
               \ for it!"

{- |
  The Prover implementation.

  Implemented are: a prover GUI, and both commandline prover interfaces.
-}
miniProver :: LP.Prover Sig.Sign AS_BASIC.FORMULA Sig.ATP_ProofTree
miniProver = LP.emptyProverTemplate
             {
               LP.prover_name             = "minisat"
             , LP.prover_sublogic         = "Prop"
             , LP.proveGUI                = Nothing
             , LP.proveCMDLautomatic      = Nothing
             , LP.proveCMDLautomaticBatch = Nothing
             }

{- |
  Record for prover specific functions. This is used by both GUI and command
  line interface.
-}
atpFun :: String            -- Theory name
       -> ATPState.ATPFunctions Sig.Sign AS_BASIC.FORMULA Sig.ATP_ProofTree PState.PropProverState
atpFun thName = ATPState.ATPFunctions
                {
                  ATPState.initialProverState = PState.propProverState
                , ATPState.goalOutput         = Cons.goalDIMACSProblem thName
                , ATPState.atpTransSenName    = PState.transSenName
                , ATPState.atpInsertSentence  = PState.insertSentence
                , ATPState.proverHelpText     = miniHelpText
                , ATPState.runProver          = runMinisat
                }

{- |
  Runs minisat. minisat is assumed to reside in PATH.
-}

runMinisat :: PState.PropProverState 
           -- logical part containing the input Sign and
           -- axioms and possibly goals that have been proved
           -- earlier as additional axioms
           -> ATPState.GenericConfig Sig.ATP_ProofTree
           -- configuration to use
           -> Bool                                     
           -- True means save DIMACS file
           -> String                                   
           -- Name of the theory
           -> AS_Anno.Named AS_BASIC.FORMULA           
           -- Goal to prove
           -> IO (ATPState.ATPRetval
                 , ATPState.GenericConfig Sig.ATP_ProofTree
                 )
           -- (retval, configuration with proof status and complete output)
runMinisat pState cfg saveDIMACS thName nGoal = 
    do
      minisat <- newChildProcess "minisat" []  
      Exception.catch (runMinisatReal minisat)
                   (\ excep -> do
                      -- kill minisat process
                      destroy minisat
                      _ <- waitForChildProcess minisat
                      excepToATPResult (LP.prover_name miniProver) nGoal excep)
    where 
      runMinisatReal minisat = 
          do 
            e <- getToolStatus minisat
            if isJust e
              then return
                     (ATPState.ATPError "Could not start minisat. Is minisat in your $PATH?",
                      ATPState.emptyConfig (LP.prover_name miniProver)
                      (AS_Anno.senName nGoal) $ Sig.ATP_ProofTree "")
              else do
                prob <- Cons.goalDIMACSProblem thName pState nGoal [] 
                when saveDIMACS
                     (writeFile (thName++'_':AS_Anno.senName nGoal++".dimacs") 
                      prob)
                sendMsg minisat prob
                error "stop"

-- | Converts a thrown exception into an ATP result (ATPRetval and proof tree).
excepToATPResult :: String 
                 -- ^ name of running prover
                 -> AS_Anno.Named AS_BASIC.FORMULA 
                 -- ^ goal to prove
                 -> Exception.Exception 
                 -- ^ occured exception
                 -> IO (ATPState.ATPRetval, 
                        ATPState.GenericConfig Sig.ATP_ProofTree) 
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
    emptyCfg = ATPState.emptyConfig prName (AS_Anno.senName nGoal) $ 
               Sig.ATP_ProofTree ""
