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

module Proofs.InferBasic (basicInferenceNode) where

import Static.GTheory
import Static.DevGraph

import Proofs.EdgeUtils
import Proofs.AbstractState
import Proofs.TheoremHideShift

import Common.ExtSign
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
import GUI.ProofManagement

import Interfaces.DataTypes
import Interfaces.Utils
import Data.IORef

import qualified Common.Lib.Graph as Tree
import Data.Graph.Inductive.Basic (elfilter)
import Data.Graph.Inductive.Graph
import Data.Maybe
import Control.Monad.Trans

getCFreeDefLinks :: DGraph -> Node
                        -> ([[LEdge DGLinkLab]], [[LEdge DGLinkLab]])
getCFreeDefLinks dg tgt =
  let isGlobalOrCFreeEdge = liftOr isGlobalEdge $ liftOr isFreeEdge isCofreeEdge
      paths = map reverse $ Tree.getAllPathsTo tgt
        $ elfilter (isGlobalOrCFreeEdge . dgl_type) $ dgBody dg
      myfilter p = filter ( \ ((_, _, lbl) : _) -> p $ dgl_type lbl)
  in (myfilter isFreeEdge paths, myfilter isCofreeEdge paths)

mkFreeDefMor :: [Named sentence] -> morphism -> morphism
                -> FreeDefMorphism sentence morphism
mkFreeDefMor sens m1 m2 = FreeDefMorphism
  { freeDefMorphism = m1
  , pathFromFreeDef = m2
  , freeTheory = sens
  , isCofree = False }

getFreeDefMorphism :: Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
   lid -> LibEnv -> LIB_NAME -> DGraph -> [LEdge DGLinkLab]
   -> Maybe (FreeDefMorphism sentence morphism)
getFreeDefMorphism lid libEnv ln dg path = case path of
  [] -> error "getFreeDefMorphism"
  (s, t, l) : rp -> do
    gmor@(GMorphism cid _ _ fmor _) <- return $ dgl_morphism l
    G_theory lidth (ExtSign _sign _) _ axs _ <-
       resultToMaybe $ computeTheory libEnv ln s
    if isHomogeneous gmor then do
        cfmor <- coerceMorphism (targetLogic cid) lid "getFreeDefMorphism1" fmor
        sens <- coerceSens lidth lid "getFreeDefMorphism4" (toNamedList axs)
        case rp of
          [] -> do
            G_theory lid2 (ExtSign sig _) _ _ _ <-
                     return $ dgn_theory $ labDG dg t
            sig2 <- coercePlainSign lid2 lid "getFreeDefMorphism2" sig
            return $ mkFreeDefMor sens cfmor $ ide sig2
          _ -> do
            pm@(GMorphism cid2 _ _ pmor _) <- calculateMorphismOfPath rp
            if isHomogeneous pm then do
                cpmor <- coerceMorphism (targetLogic cid2) lid
                         "getFreeDefMorphism3" pmor
                return $ mkFreeDefMor sens cfmor cpmor
              else Nothing
      else Nothing

getCFreeDefMorphs :: Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
   lid -> LibEnv -> LIB_NAME -> DGraph -> Node
   -> [FreeDefMorphism sentence morphism]
getCFreeDefMorphs lid libEnv ln dg node = let
  (frees, cofrees) = getCFreeDefLinks dg node
  myget = catMaybes . map (getFreeDefMorphism lid libEnv ln dg)
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
           -> [FreeDefMorphism sentence morphism]
           -> IO([Proof_status proof_tree])
cons_check _ =
    fromMaybe (\ _ _ -> fail "proveGUI not implemented") . proveGUI

proveTheory :: Logic lid sublogics
              basic_spec sentence symb_items symb_map_items
              sign morphism symbol raw_symbol proof_tree
           => lid -> Prover sign sentence morphism sublogics proof_tree
           -> String -> Theory sign sentence proof_tree
           -> [FreeDefMorphism sentence morphism]
           -> IO([Proof_status proof_tree])
proveTheory _ =
    fromMaybe (\ _ _ -> fail "proveGUI not implemented") . proveGUI


{- | applies basic inference to a given node. The result is a theory which is
     either a model after a consistency check or a new theory for the node
     label -}
basicInferenceNode :: Bool -- ^ True = consistency; False = Prove
                   -> LogicGraph -> LIB_NAME -> DGraph -> LNode DGNodeLab
                   -> GUIMVar -> LibEnv -> IORef IntState
                   -> IO (Result G_theory)
basicInferenceNode checkCons lg ln dGraph n@(node, lbl) guiMVar libEnv intSt =
  runResultT $ do
        -- compute the theory of the node, and its name
        -- may contain proved theorems
        thForProof@(G_theory lid1 (ExtSign sign _) _ axs _) <-
             liftR $ computeLabelTheory libEnv dGraph n
        let thName = shows (getLIB_ID ln) "_" ++ getDGNodeName lbl
            sens = toNamedList axs
            sublogic = sublogicOfTh thForProof
        -- select a suitable translation and prover

            cms = filter hasModelExpansion $ findComorphismPaths lg sublogic
        if checkCons then if null sens then fail $ unlines
               [ "Theory has no sentences so is trivially consistent"
               , "or incomplete due to incoming hiding links." ]
                else do
            (G_cons_checker lid4 cc, Comorphism cid) <-
                 selectProver $ getConsCheckers cms
            let lidT = targetLogic cid
                lidS = sourceLogic cid
            bTh'@(sig1, _) <- coerceBasicTheory lid1 lidS ""
                   (sign, sens)
            -- Borrowing?: translate theory
            (sig2, sens2) <- liftR $ wrapMapTheory cid bTh'
            incl <- liftR $ subsig_inclusion lidT (empty_signature lidT) sig2
            let mor = TheoryMorphism
                      { t_source = empty_theory lidT,
                        t_target = Theory sig2 $ toThSens sens2,
                        t_morphism = incl }
            cc' <- coerceConsChecker lid4 lidT "" cc
            pts <- lift $ cons_check lidT cc' thName mor
                $ getCFreeDefMorphs lidT libEnv ln dGraph node
            liftR $ case pts of
                  [pt] -> case goalStatus pt of
                    Proved (Just True) -> let
                      Result ds ms = extractModel cid sig1 $ proofTree pt
                      in case ms of
                      Nothing -> Result ds Nothing
                      Just (sig3, sens3) -> Result ds $ Just $
                         G_theory lidS (mkExtSign sig3) startSigId
                              (toThSens sens3) startThId
                    st -> fail $ "prover status is: " ++ show st
                  _ -> fail "no unique cons checkers found"
          else do
            let freedefs = getCFreeDefMorphs lid1 libEnv ln dGraph node
            kpMap <- liftR knownProversGUI
            newTh <- ResultT $
                   proofManagementGUI lid1 ProofActions
                     { proveF = proveKnownPMap lg intSt freedefs
                     , fineGrainedSelectionF =
                           proveFineGrainedSelect lg intSt freedefs
                     , recalculateSublogicF  =
                                     recalculateSublogicAndSelectedTheory
                     } thName (hidingLabelWarning lbl) thForProof
                       kpMap (getProvers ProveGUI sublogic cms) guiMVar
            return newTh

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
proveKnownPMap lg intSt  freedefs st =
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
    -> (G_prover,AnyComorphism) -> IO (Result (ProofState lid sentence))
callProver st intSt trans_chosen freedefs p_cm@(_,acm) =
       runResultT $ do
        G_theory_with_prover lid th p <- liftR $ prepareForProving st p_cm
        let freedefs1 = fromMaybe [] $
                  mapM (coerceFreeDefMorphism (logicId st) lid
                           "Logic.InferBasic: callProver")
                          freedefs
        ps <- lift $ proveTheory lid p (theoryName st) th freedefs1
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
               else getProvers ProveGUI sl $
                      filter hasModelExpansion $ findComorphismPaths lg sl
       pr <- selectProver cmsToProvers
       ResultT $ callProver st{lastSublogic = sublogicOfTheory st,
                               comorphismsToProvers = cmsToProvers}
                               intSt True freedefs pr
