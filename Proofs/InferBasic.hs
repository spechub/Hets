{- |
Module      :  $Header$
Description :  devGraph rule that calls provers for specific logics
Copyright   :  (c) J. Gerken, T. Mossakowski, K. Luettich, Uni Bremen 2002-2006
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

module Proofs.InferBasic (basicInferenceNode, basicInferenceSubTree) where

import Static.GTheory
import Static.DevGraph
import Proofs.DGFlattening(singleTree_flattening_dunions)

import Proofs.EdgeUtils
import Proofs.AbstractState
import Proofs.TheoremHideShift

import Common.ExtSign
import Common.LibName
import Common.Result
import Common.ResultT

import Control.Monad.Trans

import Logic.Logic
import Logic.Prover
import Logic.Grothendieck
import Logic.Comorphism
import Logic.Coerce

import Comorphisms.KnownProvers

import GUI.Utils
import GUI.ProofManagement
import GUI.History(CommandHistory, addProveToHist)

import qualified Common.Lib.Graph as Tree
import Data.Graph.Inductive.Basic (elfilter)
import Data.Graph.Inductive.Graph
import Data.Maybe
import qualified Data.Map as Map

isFreeEdge :: DGLinkType -> Bool
isFreeEdge edge = case edge of
    FreeDef _ -> True
    _ -> False

isCofreeEdge :: DGLinkType -> Bool
isCofreeEdge edge = case edge of
    CofreeDef _ -> True
    _ -> False

getCFreeDefLinks :: DGraph -> Node
                        -> ([[LEdge DGLinkLab]], [[LEdge DGLinkLab]])
getCFreeDefLinks dg tgt =
  let isGlobalOrCFreeEdge = liftOr isGlobalEdge $ liftOr isFreeEdge isCofreeEdge
      paths = map reverse $ Tree.getAllPathsTo tgt
        $ elfilter (isGlobalOrCFreeEdge . dgl_type) $ dgBody dg
      myfilter p = filter ( \ ((_, _, lbl) : _) -> p $ dgl_type lbl)
  in (myfilter isFreeEdge paths, myfilter isCofreeEdge paths)

mkFreeDefMor :: morphism -> morphism -> FreeDefMorphism morphism
mkFreeDefMor m1 m2 = FreeDefMorphism
  { freeDefMorphism = m1
  , pathFromFreeDef = m2
  , isCofree = False }

getFreeDefMorphism :: Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
   lid -> DGraph -> [LEdge DGLinkLab] -> Maybe (FreeDefMorphism morphism)
getFreeDefMorphism lid dg path = case path of
  [] -> error "getFreeDefMorphism"
  (_, t, l) : rp -> do
    gmor@(GMorphism cid _ _ fmor _) <- return $ dgl_morphism l
    if isHomogeneous gmor then do
        cfmor <- coerceMorphism (targetLogic cid) lid "getFreeDefMorphism1" fmor
        case rp of
          [] -> do
            G_theory lid2 (ExtSign sig _) _ _ _ <-
                     return $ dgn_theory $ labDG dg t
            sig2 <- coercePlainSign lid2 lid "getFreeDefMorphism2" sig
            return $ mkFreeDefMor cfmor $ ide sig2
          _ -> do
            pm@(GMorphism cid2 _ _ pmor _) <- calculateMorphismOfPath rp
            if isHomogeneous pm then do
                cpmor <- coerceMorphism (targetLogic cid2) lid
                         "getFreeDefMorphism3" pmor
                return $ mkFreeDefMor cfmor cpmor
              else Nothing
      else Nothing

getCFreeDefMorphs :: Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
   lid -> DGraph -> Node  -> [FreeDefMorphism morphism]
getCFreeDefMorphs lid dg node = let
  (frees, cofrees) = getCFreeDefLinks dg node
  myget = catMaybes . map (getFreeDefMorphism lid dg)
  mkCoFree m = m { isCofree = True }
  in myget frees ++ map mkCoFree (myget cofrees)

selectProver :: GetPName a => [(a, AnyComorphism)]
             -> ResultT IO (a, AnyComorphism)
selectProver ps = case ps of
  [] -> fail "No prover available"
  [p] -> return p
  _ -> do
   sel <- lift $ listBox "Choose a translation to a prover-supported logic"
     $ map (\ (aGN, cm) -> shows cm $ " (" ++ getPName aGN ++ ")") ps
   i <- case sel of
           Just j -> return j
           _ -> fail "Proofs.Proofs: selection"
   return $ ps !! i

cons_check :: Logic lid sublogics
              basic_spec sentence symb_items symb_map_items
              sign morphism symbol raw_symbol proof_tree
           => lid -> ConsChecker sign sentence sublogics morphism proof_tree
           -> String -> TheoryMorphism sign sentence morphism proof_tree
           -> [FreeDefMorphism morphism]
           -> IO([Proof_status proof_tree])
cons_check _ c =
    maybe (\ _ _ -> fail "proveGUI not implemented") id (proveGUI c)

proveTheory :: Logic lid sublogics
              basic_spec sentence symb_items symb_map_items
              sign morphism symbol raw_symbol proof_tree
           => lid -> Prover sign sentence morphism sublogics proof_tree
           -> String -> Theory sign sentence proof_tree
           -> [FreeDefMorphism morphism]
           -> IO([Proof_status proof_tree])
proveTheory _ p =
    maybe (\ _ _ -> fail "proveGUI not implemented") id (proveGUI p)


-- | applies basic inference to a given node
basicInferenceNode :: Bool -- ^ True = CheckConsistency; False = Prove
                   -> LogicGraph -> (LIB_NAME,Node) -> LIB_NAME
                   -> GUIMVar -> LibEnv -> CommandHistory
                   -> IO (Result (LibEnv, Result G_theory))
basicInferenceNode checkCons lg (ln, node) libname guiMVar libEnv ch = do
      let dGraph = lookupDGraph libname libEnv
      runResultT $ do
        -- compute the theory of the node, and its name
        -- may contain proved theorems
        (libEnv', thForProof@(G_theory lid1 (ExtSign sign _) _ axs _)) <-
             liftR $ computeTheory False libEnv ln node
        let thName = shows (getLIB_ID ln) "_"
                     ++ getNameOfNode node dGraph
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
              $ getCFreeDefMorphs lidT dGraph node
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
             -- ??? Borrowing to be implemented
            return (libEnv', resT)
          else do -- proving
            -- get known Provers

-----------------------------------------------------------------------------
{- GOALS:
          1. Make a function that writes everything to files
          2. Add it to definition of ProverTemplate
          3. Implement it with BasicInference to avoid GUI stuff
          4. Add it to definition of IsaProve -}
            kpMap <- liftR $ knownProversGUI
            newTh <- ResultT $
                   proofManagementGUI lid1 ProofActions {
                       proveF = (proveKnownPMap lg ch),
                       fineGrainedSelectionF = (proveFineGrainedSelect lg ch),
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
                nextDGraph = changeDGH dGraph $ SetNodeLab oldContents
                                         (node, newContents)
            return ( Map.insert libname nextDGraph libEnv'
                   , Result [] Nothing)

-- | applies basic inference to a given node and whole import tree above
basicInferenceSubTree :: Bool -- ^ True = CheckConsistency; False = Prove
                   -> LogicGraph
                   -> (LIB_NAME,Node)
                   -> GUIMVar
                   -> CommandHistory
                   -> LibEnv
                   -> IO (Result (LibEnv, Result G_theory))
basicInferenceSubTree checkCons lg (ln, node) guiMVar ch libEnv = do
      let dGraph = lookupDGraph ln libEnv
      runResultT $ do
        -- compute the theory of the node, and its name
        -- may contain proved theorems
        (libEnv', thForProof@(G_theory lid1 (ExtSign sign _) _ axs _)) <-
             liftR $ computeTheory False libEnv ln node
        let thName = shows (getLIB_ID ln) "_"
                     ++ getNameOfNode node dGraph
            sublogic = sublogicOfTh thForProof
        -- select a suitable translation and prover
            cms = filter hasModelExpansion $ findComorphismPaths lg sublogic
        -- incoming nodes consideration
            in_nds = map (\ (x,_,_) -> x) (innDG dGraph node)
            in_labs = map (\ x -> (x,labDG dGraph x)) in_nds
            in_theories = map (\ (x,y) -> (x,y,dgn_theory y)) in_labs
            in_sublogics = map (\ (x,y,z) -> (x,y,z,sublogicOfTh z)) in_theories
            in_cms = map (\ (x,y,z,t) ->
              (x,y,z,filter (\ cm -> elem cm (propagateErrors isaComorphisms))
                    $ findComorphismPaths lg t)) in_sublogics
            in_changed = map (\ (x,y,z,t) -> case t of
                [] ->    return $ error "no comorphism's found"
                hd : _ -> do
                  n_theory <- mapG_theory hd z
                  return $ SetNodeLab y (x,y {dgn_theory = n_theory})) in_cms
            u_dGraph = changesDGH dGraph (map propagateErrors in_changed)
            n_dGraph = groupHistory dGraph (DGRule "BasicInference-Conjectured")
                       u_dGraph
            f_libEnv = propagateErrors $ singleTree_flattening_dunions
                       (Map.insert ln n_dGraph libEnv') ln node
            f_dGraph = lookupDGraph ln f_libEnv
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
              $ getCFreeDefMorphs lidT f_dGraph node
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
             -- ??? to be implemented
            return (f_libEnv, resT)
          else do -- proving
            -- get known Provers
            kpMap <- liftR $ knownProversGUI
            newTh <- ResultT $
                   proofManagementGUI lid1 ProofActions {
                       proveF = (proveKnownPMap lg ch),
                       fineGrainedSelectionF = (proveFineGrainedSelect lg ch),
                       recalculateSublogicF  =
                                     recalculateSublogicAndSelectedTheory }
                                           thName
                                           (addHasInHidingWarning f_dGraph node)
                                           thForProof
                                           kpMap
                                           (getProvers ProveGUI sublogic cms)
                                           guiMVar
            -- update the development graph
            -- todo: throw out the stuff about edges
            -- instead, mark proven things as proven in the node
            -- TODO: Reimplement stuff
            let
                oldContents = labDG f_dGraph node
                newContents = oldContents{dgn_theory = newTh}
                -- update the graph with the new node lab
                nextDGraph = changeDGH f_dGraph $ SetNodeLab oldContents
                                         (node, newContents)
            return (Map.insert ln nextDGraph f_libEnv, Result [] Nothing)

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
       LogicGraph -> CommandHistory
    -> ProofState lid sentence -> IO (Result (ProofState lid sentence))
proveKnownPMap lg ch st =
    maybe (proveFineGrainedSelect lg ch st) (callProver st ch False) $
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
    -> CommandHistory -> Bool -- indicates if a translation was chosen
    -> (G_prover,AnyComorphism) -> IO (Result (ProofState lid sentence))
callProver st ch trans_chosen p_cm@(_,acm) =
       runResultT $ do
        G_theory_with_prover lid th p <- liftR $ prepareForProving st p_cm
        ps <- lift $ proveTheory lid p (theoryName st) th [] -- TODO: freedefs
        -- lift $ putStrLn $ show ps
        let st' = markProved acm lid ps st
        lift $ addProveToHist ch st'
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
       LogicGraph -> CommandHistory
    -> ProofState lid sentence -> IO (Result (ProofState lid sentence))
proveFineGrainedSelect lg ch st =
    runResultT $ do
       let sl = sublogicOfTheory st
           cmsToProvers =
             if sl == lastSublogic st
               then comorphismsToProvers st
               else getProvers ProveGUI sl $
                      filter hasModelExpansion $ findComorphismPaths lg sl
       pr <- selectProver cmsToProvers
       ResultT $ callProver st{lastSublogic = sublogicOfTheory st,
                               comorphismsToProvers = cmsToProvers} ch True pr
