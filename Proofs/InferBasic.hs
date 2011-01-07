{- |
Module      :  $Header$
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

selectProver :: [(G_prover, AnyComorphism)]
             -> ResultT IO (G_prover, AnyComorphism)
selectProver ps = case ps of
  [] -> fail "No prover available"
  [p] -> return p
  _ -> do
   sel <- lift $ listBox "Choose a translation to a prover-supported logic"
     $ map (\ (aGN, cm) -> shows cm $ " (" ++ getProverName aGN ++ ")") ps
   i <- case sel of
           Just j -> return j
           _ -> fail "Proofs.Proofs: selection"
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
    fromMaybe (\ _ _ -> fail "proveGUI not implemented") . proveGUI


{- | applies basic inference to a given node. The result is a theory which is
     either a model after a consistency check or a new theory for the node
     label -}
basicInferenceNode :: LogicGraph -> LibName -> DGraph -> LNode DGNodeLab
                   -> LibEnv -> IORef IntState
                   -> IO (Result G_theory)
basicInferenceNode lg ln dGraph (node, lbl) libEnv intSt =
  runResultT $ do
    -- compute the theory (that may contain proved theorems) and its name
    thForProof@(G_theory lid1 _ _ _ _) <- liftR $ getGlobalTheory lbl
    let thName = shows (getLibId ln) "_" ++ getDGNodeName lbl
        sublogic = sublogicOfTh thForProof
    -- select a suitable translation and prover
        cms = filter hasModelExpansion $ findComorphismPaths lg sublogic
        freedefs = getCFreeDefMorphs lid1 libEnv ln dGraph node
    kpMap <- liftR knownProversGUI
    ResultT $ proverGUI lid1 ProofActions
      { proveF = proveKnownPMap lg intSt freedefs
      , fineGrainedSelectionF = proveFineGrainedSelect lg intSt freedefs
      , recalculateSublogicF = return . recalculateSublogicAndSelectedTheory
      } thName (hidingLabelWarning lbl) thForProof kpMap
      (getProvers ProveGUI (Just sublogic) cms)

proveKnownPMap :: (Logic lid sublogics1
               basic_spec1
               sentence
               symb_items1
               symb_map_items1
               sign1
               morphism1
               symbol1
               raw_symbol1
               proof_tree1) =>
       LogicGraph
    -> IORef IntState
    -> [FreeDefMorphism sentence morphism1]
    -> ProofState lid sentence -> IO (Result (ProofState lid sentence))
proveKnownPMap lg intSt freedefs st =
    maybe (proveFineGrainedSelect lg intSt freedefs st)
          (callProver st intSt False freedefs) $
          lookupKnownProver st ProveGUI

callProver :: (Logic lid sublogics1
               basic_spec1
               sentence
               symb_items1
               symb_map_items1
               sign1
               morphism1
               symbol1
               raw_symbol1
               proof_tree1) =>
       ProofState lid sentence
    -> IORef IntState
    -> Bool -- indicates if a translation was chosen
    -> [FreeDefMorphism sentence morphism1]
    -> (G_prover, AnyComorphism) -> IO (Result (ProofState lid sentence))
callProver st intSt trans_chosen freedefs p_cm@(_, acm) =
       runResultT $ do
        (_, exit) <- lift $ pulseBar "prepare for proving" "please wait..."
        G_theory_with_prover lid th p <- liftR $ prepareForProving st p_cm
        let freedefs1 = fromMaybe [] $ mapM (coerceFreeDefMorphism (logicId st)
                                            lid "Logic.InferBasic: callProver")
                                            freedefs
        lift exit
        (ps, _) <- lift $ proveTheory lid p (theoryName st) th freedefs1
        let st' = markProved acm lid ps st
        lift $ addCommandHistoryToState intSt st'
              (if trans_chosen then Just p_cm else Nothing) ps
        return st'

proveFineGrainedSelect ::
    (Logic lid sublogics1
               basic_spec1
               sentence
               symb_items1
               symb_map_items1
               sign1
               morphism1
               symbol1
               raw_symbol1
               proof_tree1) =>
       LogicGraph
    -> IORef IntState
    -> [FreeDefMorphism sentence morphism1]
    -> ProofState lid sentence -> IO (Result (ProofState lid sentence))
proveFineGrainedSelect lg intSt freedefs st =
    runResultT $ do
       let sl = sublogicOfTheory st
           cmsToProvers =
             if sl == lastSublogic st
               then comorphismsToProvers st
               else getProvers ProveGUI (Just sl) $
                      filter hasModelExpansion $ findComorphismPaths lg sl
       pr <- selectProver cmsToProvers
       ResultT $ callProver st {lastSublogic = sublogicOfTheory st,
                               comorphismsToProvers = cmsToProvers}
                               intSt True freedefs pr
