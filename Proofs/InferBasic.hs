{- |
Module      :  $Header$
Copyright   :  (c) J. Gerken, T. Mossakowski, K. Lüttich, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Description :  inference with a prover in a specific logic
Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

Proof rule "basic inference" in the development graphs calculus.
   Follows Sect. IV:4.4 of the CASL Reference Manual.
-}

{-
   References:

   T. Mossakowski, S. Autexier and D. Hutter:
   Extending Development Graphs With Hiding.
   H. Hussmann (ed.): Fundamental Approaches to Software Engineering 2001,
   Lecture Notes in Computer Science 2029, p. 269-283,
   Springer-Verlag 2001.

todo:

do not add new dg nodes, but just change the old one

Integrate stuff from Saarbrücken (what exactly?)

-}

module Proofs.InferBasic (basicInferenceNode, getGoals, GetPName()) where

import Static.DevGraph
import Static.DGToSpec

import Syntax.AS_Library
import Syntax.Print_AS_Library()

import Proofs.StatusUtils
import Proofs.EdgeUtils
import Proofs.GUIState

import Common.Id
import Common.Result
import Common.ResultT
import Common.Utils

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.OrderedMap as OMap

import Control.Monad.Trans
import Data.Graph.Inductive.Graph
import Data.List (find)

import Logic.Logic
import Logic.Prover
import Logic.Grothendieck
import Logic.Comorphism
import Logic.Coerce

import Comorphisms.KnownProvers

import GUI.Utils
import GUI.ProofManagement

-- ---------------
-- basic inference
-- ---------------

getGoals :: LibEnv -> LIB_NAME -> LEdge DGLinkLab
         -> Result G_theory
getGoals libEnv ln (n,_,edge) = do
  th <- computeLocalTheory libEnv ln n
  translateG_theory (dgl_morphism edge) th

class GetPName a where
    getPName :: a -> String

instance GetPName G_prover where
    getPName (G_prover _ p) = prover_name p

instance GetPName G_cons_checker where
    getPName (G_cons_checker _ p) = prover_name p

-- | Pairs each target prover of these comorphisms with its comorphism
getProvers :: [AnyComorphism] -> [(G_prover, AnyComorphism)]
getProvers = foldl addProvers []
    where addProvers acc cm =
              case cm of
              Comorphism cid -> acc ++
                  foldl (\ l p -> if hasProverKind ProveGUI p 
                                     then (G_prover (targetLogic cid) p,cm):l
                                     else l)
                        []
                        (provers $ targetLogic cid)


{-     [(G_prover (targetLogic cid) p, cm) |
        cm@(Comorphism cid) <- cms,
        p <- provers (targetLogic cid)]
-}
getConsCheckers :: [AnyComorphism] -> [(G_cons_checker, AnyComorphism)]
getConsCheckers = foldl addCCs []
    where addCCs acc cm =
              case cm of
              Comorphism cid -> acc ++
                  map (\p -> (G_cons_checker (targetLogic cid) p,cm))
                      (cons_checkers $ targetLogic cid)

selectProver :: GetPName a =>
                [(a,AnyComorphism)] -> ResultT IO (a,AnyComorphism)
selectProver [p] = return p
selectProver [] = liftR $ fatal_error "No prover available" nullRange
selectProver ps = do
   sel <- lift $ listBox
                "Choose a translation to a prover-supported logic"
                $ map (\ (aGN,cm) -> show cm ++" ("++getPName aGN++")") ps
   i <- case sel of
           Just j -> return j
           _ -> liftR $ fail "Proofs.Proofs: selection"
   return $ ps !! i

cons_check :: Logic lid sublogics
              basic_spec sentence symb_items symb_map_items
              sign morphism symbol raw_symbol proof_tree
           => lid -> ConsChecker sign sentence morphism proof_tree
           -> String -> TheoryMorphism sign sentence morphism proof_tree
           -> IO([Proof_status proof_tree])
cons_check _ c = 
    maybe (\ _ _ -> fail "proveGUI not implemented") id (proveGUI c)

proveTheory :: Logic lid sublogics
              basic_spec sentence symb_items symb_map_items
              sign morphism symbol raw_symbol proof_tree
           => lid -> Prover sign sentence proof_tree
           -> String -> Theory sign sentence proof_tree
           -> IO([Proof_status proof_tree])
proveTheory _ p = 
    maybe (\ _ _ -> fail "proveGUI not implemented") id (proveGUI p)
                

-- | applies basic inference to a given node
basicInferenceNode :: Bool -> LogicGraph -> (LIB_NAME,Node) -> LIB_NAME
                   -> GUIMVar -> LibEnv -> IO (Result LibEnv)
basicInferenceNode checkCons lg (ln, node) libname guiMVar libEnv = do
      let dGraph = lookupDGraph libname libEnv
      runResultT $ do
        -- compute the theory of the node, and its name
        -- may contain proved theorems
        thForProof@(G_theory lid1 sign _ axs _) <-
             liftR $ computeTheory libEnv ln node
        ctx <- liftR
                    $ maybeToMonad ("Could not find node "++show node)
                    $ fst $ match node dGraph
        let nodeName = dgn_name $ lab' ctx
            thName = shows (getLIB_ID ln) "_"
                     ++ {-maybe (show node)-} showName nodeName
            sublogic = sublogicOfTh thForProof
        -- select a suitable translation and prover
            cms = findComorphismPaths lg sublogic
        if checkCons then do
            (G_cons_checker lid4 cc, Comorphism cid) <-
                 selectProver $ getConsCheckers cms
            bTh' <- coerceBasicTheory lid1 (sourceLogic cid) ""
                   (sign, toNamedList axs)
            -- Borrowing: translate theory
            (sign'', sens'') <- liftR $ map_theory cid bTh'
            let lidT = targetLogic cid
            incl <- liftR $ inclusion lidT (empty_signature lidT) sign''
            let mor = TheoryMorphism
                      { t_source = empty_theory lidT,
                        t_target = Theory sign'' (toThSens sens''),
                        t_morphism = incl }
            cc' <- coerceConsChecker lid4 lidT "" cc
            lift $ cons_check lidT cc' thName mor
            let nextHistoryElem = ([LocalInference],[])
             -- ??? to be implemented
                newProofStatus = mkResultProofStatus libname
                                 libEnv dGraph nextHistoryElem
            return newProofStatus
          else do -- proving
            -- get known Provers
            kpMap <- liftR $ knownProversGUI
            let kpMap' = shrinkKnownProvers sublogic kpMap
            newTh <- ResultT $
                   proofManagementGUI lid1 proveKnownPMap
                                           proveFineGrainedSelect
                                           thName
                                           thForProof
                                           kpMap'
                                           (getProvers cms)
                                           guiMVar
            -- update the development graph
            -- todo: throw out the stuff about edges
            -- instead, mark proven things as proven in the node
            -- TODO: Reimplement stuff
            let oldNode@(_,oldContents) =
                    labNode' (safeContext
                              "Proofs.InferBasic.basicInferenceNode"
                              dGraph node)
                newNodeLab = oldContents{dgn_theory = newTh}
                (nextDGraph,changes) =
                    adjustNode dGraph oldNode newNodeLab
                rules = [] -- map (\s -> BasicInference (Comorphism cid)
                           --     (BasicProof lidT s))
                         -- FIXME: [Proof_status] not longer available
                nextHistoryElem = (rules,changes)
            return $ mkResultProofStatus libname libEnv
                   nextDGraph nextHistoryElem

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
       ProofGUIState lid sentence -> IO (Result (ProofGUIState lid sentence))
proveKnownPMap st =
    let mt = do
           pr_s <- selectedProver st
           ps <- Map.lookup pr_s (proversMap st)
           cm <- find (lessSublogicComor (sublogicOfTheory st)) ps
           return (pr_s,cm)
        matchingPr s (gp,_) = case gp of
                               G_prover _ p -> prover_name p == s
    in case mt of
       Nothing -> proveFineGrainedSelect st
       Just (pr_n,cm) ->
           callProver st
                      (case filter (matchingPr pr_n) $
                            getProvers [cm] of
                       [] -> error "Proofs.InferBasic: no prover found"
                       [p] -> p
                       _ -> error $ "Proofs.InferBasic: more than one"++
                                    " matching prover found")

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
       ProofGUIState lid sentence
    -> (G_prover,AnyComorphism) -> IO (Result (ProofGUIState lid sentence))
callProver st (G_prover lid4 p, Comorphism cid) =
    case theory st of
    G_theory lid1 sign _ sens _ ->
        runResultT $ do
          -- coerce goalMap
        ths <- coerceThSens (logicId st) lid1
                            "Proofs.InferBasic.callProver: selected goals"
                            (goalMap st)
          -- partition goalMap
        let (sel_goals,other_goals) =
                let selected k _ = Set.member k s
                    s = Set.fromList (selectedGoals st)
                in Map.partitionWithKey selected ths
            provenThs =
                   Map.filter (\x -> (isProvenSenStatus $ OMap.ele x))
                   other_goals
          -- select goals from goalMap
            -- sel_goals = filterMapWithList (selectedGoals st) goals
          -- select proven theorems from goalMap
            sel_provenThs = OMap.map (\ x -> x{isAxiom = True}) $
                            filterMapWithList (includedTheorems st) provenThs
            sel_sens = filterMapWithList (includedAxioms st) sens
            lidT = targetLogic cid
        bTh' <- coerceBasicTheory lid1 (sourceLogic cid)
                   "Proofs.InferBasic.callProver: basic theory"
                   (sign, toNamedList $
                          Map.union sel_sens $
                          Map.union sel_provenThs sel_goals)
        (sign'',sens'') <- liftR $ map_theory cid bTh'
        -- call the prover
        p' <- coerceProver lid4 lidT "" p
        ps <- lift (proveTheory lidT p' (theoryName st)
                           (Theory sign'' (toThSens sens'')))
        -- lift $ putStrLn $ show ps
        return $ st { goalMap =
                          markProved (Comorphism cid) lidT
                                     (filter (provedOrDisproved
                                              (includedAxioms st ==
                                               OMap.keys sens)) ps)
                                     (goalMap st)
                    }
    where provedOrDisproved allSentencesIncluded senStat =
              isProvedStat senStat ||
             (allSentencesIncluded && case goalStatus senStat of
                                      Disproved -> True
                                      _ -> False)

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
       ProofGUIState lid sentence -> IO (Result (ProofGUIState lid sentence))
proveFineGrainedSelect st =
    runResultT $ do
       pr <- selectProver $ comorphismsToProvers st
       ResultT $ callProver st pr

-- | mark all newly proven goals with their proof tree
markProved :: (Ord a, Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree) =>
       AnyComorphism -> lid -> [Proof_status proof_tree]
    -> ThSens a (AnyComorphism,BasicProof)
    -> ThSens a (AnyComorphism,BasicProof)
markProved c lid status thSens = foldl upd thSens status
    where upd m pStat = OMap.update (updStat pStat) (goalName pStat) m
          updStat ps s = Just $
                s { thmStatus = (c, BasicProof lid ps) : thmStatus s}

