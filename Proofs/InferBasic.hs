{- |
Module      :  $Header$
Description :  devGraph rule that calls provers for specific logics
Copyright   :  (c) J. Gerken, T. Mossakowski, K. Lüttich, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
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

module Proofs.InferBasic (basicInferenceNode) where

import Static.GTheory
import Static.DevGraph


import Syntax.AS_Library
import Syntax.Print_AS_Library()

import Proofs.StatusUtils
import Proofs.EdgeUtils
import Proofs.AbstractState
import Proofs.TheoremHideShift

import Common.ExtSign
import Common.Id
import Common.Result
import Common.ResultT

import Control.Monad.Trans
import Data.Graph.Inductive.Graph

import Logic.Logic
import Logic.Prover
import Logic.Grothendieck
import Logic.Comorphism
import Logic.Coerce

import Comorphisms.KnownProvers

import GUI.Utils
import GUI.ProofManagement

import Data.Maybe
-- ---------------
-- basic inference
-- ---------------

selectProver :: GetPName a =>
                [(a,AnyComorphism)] -> ResultT IO (a,AnyComorphism)
selectProver [p] = return p
selectProver [] = fail "No prover available"
selectProver ps = do
   sel <- lift $ listBox
                "Choose a translation to a prover-supported logic"
                $ map (\ (aGN,cm) -> show cm ++" ("++getPName aGN++")") ps
   i <- case sel of
           Just j -> return j
           _ -> fail "Proofs.Proofs: selection"
   return $ ps !! i

cons_check :: Logic lid sublogics
              basic_spec sentence symb_items symb_map_items
              sign morphism symbol raw_symbol proof_tree
           => lid -> ConsChecker sign sentence sublogics morphism proof_tree
           -> String -> TheoryMorphism sign sentence morphism proof_tree
           -> IO([Proof_status proof_tree])
cons_check _ c =
    maybe (\ _ _ -> fail "proveGUI not implemented") id (proveGUI c) []

proveTheory :: Logic lid sublogics
              basic_spec sentence symb_items symb_map_items
              sign morphism symbol raw_symbol proof_tree
           => lid -> Prover sign sentence sublogics proof_tree
           -> String -> Theory sign sentence proof_tree
           -> IO([Proof_status proof_tree])
proveTheory _ p =
    maybe (\ _ _ -> fail "proveGUI not implemented") id (proveGUI p) []


-- | applies basic inference to a given node
basicInferenceNode :: Bool -- ^ True = CheckConsistency; False = Prove
                   -> LogicGraph -> (LIB_NAME,Node) -> LIB_NAME
                   -> GUIMVar -> LibEnv
                   -> IO (Result (LibEnv, Result G_theory))
basicInferenceNode checkCons lg (ln, node) libname guiMVar libEnv = do
      let dGraph = lookupDGraph libname libEnv
      runResultT $ do
        -- compute the theory of the node, and its name
        -- may contain proved theorems
        (libEnv', thForProof@(G_theory lid1 (ExtSign sign _) _ axs _)) <-
             liftR $ computeTheory False libEnv ln node
        ctx <- liftR
                    $ maybeToMonad ("Could not find node "++show node)
                    $ fst $ matchDG node dGraph
        let nodeName = dgn_name $ lab' ctx
            thName = shows (getLIB_ID ln) "_"
                     ++ {-maybe (show node)-} showName nodeName
            sublogic = sublogicOfTh thForProof
        -- select a suitable translation and prover

            cms = filter hasModelExpansion $ findComorphismPaths lg sublogic
        if checkCons then do
            (G_cons_checker lid4 cc, Comorphism cid) <-
                 selectProver $ getConsCheckers cms
            let lidT = targetLogic cid
                lidS = sourceLogic cid
            bTh'@(sign', _) <- coerceBasicTheory lid1 lidS ""
                   (sign, toNamedList axs)
            -- Borrowing: translate theory
            (sign'', sens'') <- liftR $ wrapMapTheory cid bTh'
            incl <- liftR $ inclusion lidT (empty_signature lidT) sign''
            let mor = TheoryMorphism
                      { t_source = empty_theory lidT,
                        t_target = Theory sign'' (toThSens sens''),
                        t_morphism = incl }
            cc' <- coerceConsChecker lid4 lidT "" cc
            pts <- lift $ cons_check lidT cc' thName mor
            let resT = case pts of
                  [pt] -> case goalStatus pt of
                    Proved (Just True) -> let
                      Result ds ms = extractModel cid sign' $ proofTree pt
                      in case ms of
                      Nothing -> Result ds Nothing
                      Just (sign''', sens''') -> Result ds $ Just $
                         G_theory lidS (mkExtSign sign''') startSigId
                              (toThSens sens''') startThId
                    _ -> Result [] Nothing
                  _ -> Result [] Nothing
            let nextHistoryElem = ([Borrowing],[])
             -- ??? to be implemented
                newProofStatus = mkResultProofStatus libname
                                 libEnv' dGraph nextHistoryElem
            return (newProofStatus, resT)
          else do -- proving
            -- get known Provers
            kpMap <- liftR $ knownProversGUI
            newTh <- ResultT $
                   proofManagementGUI lid1 ProofActions {
                       proveF = (proveKnownPMap lg),
                       fineGrainedSelectionF = (proveFineGrainedSelect lg),
                       recalculateSublogicF  =
                                     recalculateSublogicAndSelectedTheory }
                                           thName
                                           (addHasInHidingWarning dGraph node)
                                           thForProof
                                           kpMap
                                           (getProvers ProveGUI sublogic cms)
                                           guiMVar
            -- update the development graph
            -- todo: throw out the stuff about edges
            -- instead, mark proven things as proven in the node
            -- TODO: Reimplement stuff
            let oldContents = labDG dGraph node
                newContents = oldContents{dgn_theory = newTh}
                -- update the graph with the new node lab
                (nextDGraph,changes) =
                    updateWithOneChange (SetNodeLab
                                      (error "basicInferenceNode")
                                         (node, newContents)) dGraph
                rules = [] -- map (\s -> BasicInference (Comorphism cid)
                           --     (BasicProof lidT s))
                         -- FIXME: [Proof_status] not longer available
                nextHistoryElem = (rules,changes)
            return (mkResultProofStatus libname libEnv'
                    nextDGraph nextHistoryElem, Result [] Nothing)

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
    -> ProofState lid sentence -> IO (Result (ProofState lid sentence))
proveKnownPMap lg st =
    maybe (proveFineGrainedSelect lg st) (callProver st) $
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
    -> (G_prover,AnyComorphism) -> IO (Result (ProofState lid sentence))
callProver st p_cm@(_,acm) =
       runResultT $ do
        G_theory_with_prover lid th p <- liftR $ prepareForProving st p_cm
        ps <- lift $ proveTheory lid p (theoryName st) th
        -- lift $ putStrLn $ show ps
        return $ markProved acm lid ps st

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
    -> ProofState lid sentence -> IO (Result (ProofState lid sentence))
proveFineGrainedSelect lg st =
    runResultT $ do
       let sl = sublogicOfTheory st
           cmsToProvers =
             if sl == lastSublogic st
               then comorphismsToProvers st
               else getProvers ProveGUI sl $
                      filter hasModelExpansion $ findComorphismPaths lg sl
       pr <- selectProver cmsToProvers
       ResultT $ callProver st{lastSublogic = sublogicOfTheory st,
                               comorphismsToProvers = cmsToProvers} pr
