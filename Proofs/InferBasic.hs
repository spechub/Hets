{- |
Module      :  ./Proofs/InferBasic.hs
Description :  devGraph rule that calls provers for specific logics
Copyright   :  (c) J. Gerken, T. Mossakowski, K. Luettich, Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Logic)

devGraph rule that calls provers for specific logics

Proof rule "basic inference" in the development graphs calculus.
   Follows Sect. IV:4.4 of the CASL Reference Manual.

   References:

   T. Mossakowski, S. Autexier and D. Hutter:
   Extending Development Graphs With Hiding.
   H. Hussmann (ed.): Fundamental Approaches to Software Engineering 2001,
   Lecture Notes in Computer Science 2029, p. 269-283,
   Springer-Verlag 2001.

-}

module Proofs.InferBasic
  ( basicInferenceNode
  ) where

import Static.GTheory
import Static.DevGraph
import Static.ComputeTheory

import Proofs.EdgeUtils
import Proofs.AbstractState
import Proofs.FreeDefLinks

import Common.LibName
import Common.Result
import Common.ResultT
import Common.AS_Annotation

import Logic.Logic
import Logic.Prover
import Logic.Grothendieck
import Logic.Comorphism
import Logic.Coerce

import Comorphisms.KnownProvers

import GUI.Utils
import GUI.ProverGUI

import Interfaces.DataTypes
import Interfaces.Utils

import Data.IORef
import Data.Graph.Inductive.Graph
import Data.Maybe

import Control.Monad.Trans
import qualified Control.Monad.Fail as Fail

selectProver :: [(G_prover, AnyComorphism)]
             -> ResultT IO (G_prover, AnyComorphism)
selectProver ps = case ps of
  [] -> Fail.fail "No prover available"
  [p] -> return p
  _ -> do
   sel <- lift $ listBox "Choose a translation to a prover-supported logic"
     $ map (\ (aGN, cm) -> shows cm $ " (" ++ getProverName aGN ++ ")") ps
   i <- case sel of
           Just j -> return j
           _ -> Fail.fail "Proofs.Proofs: selection"
   return $ ps !! i

proveTheory :: Logic lid sublogics
              basic_spec sentence symb_items symb_map_items
              sign morphism symbol raw_symbol proof_tree
           => lid -> Prover sign sentence morphism sublogics proof_tree
           -> String -> Theory sign sentence proof_tree
           -> [FreeDefMorphism sentence morphism]
           -> IO ( [ProofStatus proof_tree]
                , [(Named sentence, ProofStatus proof_tree)])
proveTheory _ =
    fromMaybe (\ _ _ -> error "proveGUI not implemented") . proveGUI


{- | applies basic inference to a given node. The result is a theory which is
     either a model after a consistency check or a new theory for the node
     label -}
basicInferenceNode :: LogicGraph -> LibName -> DGraph -> LNode DGNodeLab
                   -> LibEnv -> IORef IntState
                   -> IO (Result G_theory)
basicInferenceNode lg ln dGraph (node, lbl) libEnv intSt =
  runResultT $ do
    -- compute the theory (that may contain proved theorems) and its name
    thForProof <- liftR $ getGlobalTheory lbl
    let thName = libToFileName ln ++ "_" ++ getDGNodeName lbl
        freedefs = getCFreeDefMorphs libEnv ln dGraph node
    ps <- lift $ getUsableProvers ProveGUI (sublogicOfTh thForProof) lg
    kpMap <- liftR knownProversGUI
    {- let kpMap = foldl (\m (G_prover _ p,c) ->
         case Map.lookup (proverName p) m of
          Just cs -> Map.insert (proverName p) (c:cs) m
          Nothing -> Map.insert (proverName p) [c] m) Map.empty ps -}
    ResultT $ proverGUI ProofActions
      { proveF = proveKnownPMap lg intSt freedefs
      , fineGrainedSelectionF = proveFineGrainedSelect lg intSt freedefs
      , recalculateSublogicF = return . recalculateSublogicAndSelectedTheory
      } thName (hidingLabelWarning lbl) thForProof kpMap ps

proveKnownPMap :: LogicGraph
    -> IORef IntState
    -> [GFreeDefMorphism]
    -> ProofState -> IO (Result ProofState)
proveKnownPMap lg intSt freedefs st =
    maybe (proveFineGrainedSelect lg intSt freedefs st)
          (callProver st intSt False freedefs) $
          lookupKnownProver st ProveGUI

callProver :: ProofState
    -> IORef IntState
    -> Bool -- indicates if a translation was chosen
    -> [GFreeDefMorphism]
    -> (G_prover, AnyComorphism) -> IO (Result ProofState)
callProver st intSt trans_chosen freedefs p_cm@(_, acm) =
       runResultT $ do
        (_, exit) <- lift $ pulseBar "prepare for proving" "please wait..."
        G_theory_with_prover lid th p <- liftR $ prepareForProving st p_cm
        freedefs1 <- mapM (\ (GFreeDefMorphism fdlid fd) ->
                       coerceFreeDefMorphism fdlid lid "" fd) freedefs
        lift exit
        (ps, _) <- lift $ proveTheory lid p (theoryName st) th freedefs1
        let st' = markProved acm lid ps st
        lift $ addCommandHistoryToState intSt st'
               (if trans_chosen then Just p_cm else Nothing) ps "" (False, 0)
        return st'

proveFineGrainedSelect :: LogicGraph
    -> IORef IntState
    -> [GFreeDefMorphism]
    -> ProofState -> IO (Result ProofState)
proveFineGrainedSelect lg intSt freedefs st =
    runResultT $ do
       let sl = sublogicOfTheory st
       cmsToProvers <- lift $ getUsableProvers ProveGUI sl lg
       pr <- selectProver cmsToProvers
       ResultT $ callProver st { comorphismsToProvers = cmsToProvers }
                               intSt True freedefs pr
