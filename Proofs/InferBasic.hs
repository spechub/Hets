{-| 
   
Module      :  $Header$
Copyright   :  (c) Jorina F. Gerken, Till Mossakowski, Klaus Lüttich, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jfgerken@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

Proofs in development graphs.
   Follows Sect. IV:4.4 of the CASL Reference Manual.
-}

{- 
   References:

   T. Mossakowski, S. Autexier and D. Hutter:
   Extending Development Graphs With Hiding.
   H. Hussmann (ed.): Fundamental Approaches to Software Engineering 2001,
   Lecture Notes in Computer Science 2029, p. 269-283,
   Springer-Verlag 2001.

todo in general:

Order of rule application: try to use local links induced by %implies 
for subsumption proofs (such that the %implied formulas need not be
re-proved)

Integrate stuff from Saarbrücken
Add proof status information

 what should be in proof status:

- proofs of thm links according to rules
- cons, def and mono annos, and their proofs

-}

module Proofs.InferBasic (automatic, basicInferenceNode) where

import Logic.Logic
import Logic.Prover
import Logic.Grothendieck
import Logic.Comorphism
import Logic.Coerce
import Static.DevGraph
import Static.DGToSpec
import Common.Result
import Common.PrettyPrint
import Common.Utils
import Data.Graph.Inductive.Graph
import qualified Common.Lib.Map as Map
import qualified Common.OrderedMap as OMap
import Common.Id
import Syntax.AS_Library
import Syntax.Print_AS_Library()
import Proofs.EdgeUtils
import Proofs.StatusUtils
import Proofs.Global
import Proofs.Local
import Proofs.HideTheoremShift
import GUI.Utils

{- todo: implement apply for GlobDecomp and Subsumption 
   the list of DGChage must be constructed in parallel to the
   new DGraph -}
applyRule :: DGRule -> DGraph -> Maybe ([DGChange],DGraph)
applyRule = error "Proofs.hs:applyRule"


{- automatically applies all rules to the library
   denoted by the library name of the given proofstatus-}
automatic :: ProofStatus -> ProofStatus
automatic = automaticRecursive 0


{- applies the rules recursively until no further changes can be made -}
automaticRecursive :: Int -> ProofStatus -> ProofStatus
automaticRecursive cnt proofstatus = 
  let auxProofstatus = automaticApplyRules proofstatus
      finalProofstatus = mergeHistories cnt auxProofstatus
  in case finalProofstatus of
    Nothing -> proofstatus
    Just p -> automaticRecursive 1 p


{- sequentially applies all rules to the given proofstatus,
   ie to the library denoted by the library name of the proofstatus -}
automaticApplyRules :: ProofStatus -> ProofStatus
automaticApplyRules p = 
   --  theoremHideShift p
  let p1 = globSubsume p
      p2 = globDecomp p1
      p3 = localInference p2
      p4 = locDecomp p3
  in automaticHideTheoremShift p4


{- merges for every library the new history elements
   to one new history element -}
mergeHistories :: Int -> ProofStatus -> Maybe ProofStatus
mergeHistories cnt proofstatus@(ln,libEnv,_) = 
  let (numChanges,newProofstatus) = mergeHistoriesAux cnt 
                                    (Map.keys libEnv) proofstatus
  in if (numChanges > 0) then 
     Just $ changeCurrentLibName ln newProofstatus
    else Nothing

{- auxiliary method for mergeHistories:
   determined the library names and recursively applies mergeHistory -}
mergeHistoriesAux :: Int -> [LIB_NAME] -> ProofStatus -> (Int,ProofStatus)
mergeHistoriesAux _ [] proofstatus = (0, proofstatus)
mergeHistoriesAux cnt (ln:list) proofstatus =
  let ps = mergeHistory cnt (changeCurrentLibName ln proofstatus)
  in case ps of
    Just newProofstatus -> let 
      (i,finalProofstatus) = mergeHistoriesAux cnt list newProofstatus
      in (i+1,finalProofstatus)
    Nothing -> mergeHistoriesAux cnt list proofstatus

{- merges the new history elements of a single library
   to one new history elemebt-}
mergeHistory :: Int -> ProofStatus -> Maybe ProofStatus
mergeHistory cnt proofstatus@(ln,libEnv,historyMap) =
  let history = lookupHistory ln proofstatus
--      dgraph = lookupDGraph ln proofstatus
      (newHistoryPart, oldHistory) = splitAt (5+cnt) history
  in if null (concatMap snd $ take 5 newHistoryPart) && cnt == 1 then
     Nothing
   else
    let (rules, changes) = concatHistoryElems (reverse newHistoryPart)
        newHistoryElem = (rules, removeContraryChanges changes)
        newHistory = newHistoryElem:oldHistory
    in Just (ln, libEnv, Map.insert ln newHistory historyMap)

{- concats the given history elements to one history element-}
concatHistoryElems :: [([DGRule],[DGChange])] -> ([DGRule],[DGChange])
concatHistoryElems [] = ([], [])
concatHistoryElems ((rules, changes) : elems) =
  (rules ++ fst (concatHistoryElems elems),
         changes ++ snd (concatHistoryElems elems))

-- ---------------
-- basic inference
-- ---------------

getGoals :: LibEnv -> LIB_NAME -> LEdge DGLinkLab 
         -> Result G_theory
getGoals libEnv ln (n,_,edge) = do
  th <- computeLocalTheory libEnv (ln, n)
  translateG_theory (dgl_morphism edge) th

getProvers :: [AnyComorphism] -> [(G_prover, AnyComorphism)]
getProvers cms =
     [(G_prover (targetLogic cid) p, cm) | 
        cm@(Comorphism cid) <- cms,
        p <- provers (targetLogic cid)]

getConsCheckers :: [AnyComorphism] -> [(G_cons_checker, AnyComorphism)]
getConsCheckers cms =
     [(G_cons_checker (targetLogic cid) p, cm) | 
        cm@(Comorphism cid) <- cms,
        p <- cons_checkers (targetLogic cid)]

selectProver :: [(a,AnyComorphism)] -> IOResult (a,AnyComorphism)
selectProver [p] = return p
selectProver [] = resToIORes $ fatal_error "No prover available" nullRange
selectProver ps = do
   sel <- ioToIORes $ listBox 
                "Choose a translation to a prover-supported logic"
                $ map (show.snd) ps
   i <- case sel of
           Just j -> return j
           _ -> resToIORes $ fail "Proofs.Proofs: selection"
   return $ ps !! i
 
cons_check :: Logic lid sublogics
              basic_spec sentence symb_items symb_map_items
              sign morphism symbol raw_symbol proof_tree 
           => lid -> ConsChecker sign sentence morphism proof_tree 
           -> String -> TheoryMorphism sign sentence morphism proof_tree
           -> IO([Proof_status proof_tree])
cons_check _ = prove

proveTheory :: Logic lid sublogics
              basic_spec sentence symb_items symb_map_items
              sign morphism symbol raw_symbol proof_tree 
           => lid -> Prover sign sentence proof_tree 
           -> String -> Theory sign sentence proof_tree 
           -> IO([Proof_status proof_tree])
proveTheory _ = prove

-- | applies basic inference to a given node
basicInferenceNode :: Bool -> LogicGraph -> (LIB_NAME,Node) -> ProofStatus 
                          -> IO (Result ProofStatus)
basicInferenceNode checkCons lg (ln, node)
         proofStatus@(libname, libEnv, _) = do
      let dGraph = lookupDGraph libname proofStatus
      ioresToIO $ do 
        -- compute the theory of the node, and its name
        -- may contain proved theorems
        G_theory lid1 sign axs <- 
             resToIORes $ computeTheory libEnv (ln, node)
        -- ioToIORes $ putStrLn ("G_theory "++show lid1++" "++show sign++" "++show axs)
        ctx <- resToIORes 
                    $ maybeToMonad ("Could not find node "++show node)
                    $ fst $ match node dGraph
        let nodeName = dgn_name $ lab' ctx 
            thName = showPretty (getLIB_ID ln) "_"
                     ++ {-maybe (show node)-} showName nodeName
        -- select a suitable translation and prover
        let cms = findComorphismPaths lg $ sublogicOfTh $ 
                     G_theory lid1 sign axs 
        if checkCons then do 
            (G_cons_checker lid4 cc, Comorphism cid) <- 
                 selectProver $ getConsCheckers cms
            bTh' <- coerceBasicTheory lid1 (sourceLogic cid) "" 
                   (sign, toNamedList axs)
            -- Borrowing: translate theory
            (sign'', sens'') <- resToIORes $ map_theory cid bTh'
            let lidT = targetLogic cid
            incl <- resToIORes $ inclusion lidT (empty_signature lidT) sign''
            let mor = TheoryMorphism { t_source = empty_theory lidT, 
                                       t_target = Theory sign'' (toThSens sens''),
                                       t_morphism = incl } 
            cc' <- coerceConsChecker lid4 lidT "" cc
            ps <- ioToIORes $ cons_check lidT cc' thName mor
            let nextHistoryElem = ([LocalInference],[])
             -- ??? to be implemented
                newProofStatus
                  = mkResultProofStatus proofStatus dGraph nextHistoryElem
            return newProofStatus
          else do -- proving
            (G_prover lid4 p, Comorphism cid) <- selectProver $ getProvers cms
            -- remove proved theorems from set of axioms
            let ax_list = toNamedList 
                           (OMap.filter (\x -> not (isProvenSenStatus x)) axs)
            let lidT = targetLogic cid
                transTh = resToIORes . map_theory cid
            bTh' <- coerceBasicTheory lid1 (sourceLogic cid) "" 
                   (sign, ax_list)
            (sign'',sens'') <- transTh bTh'
            -- call the prover
            p' <- coerceProver lid4 lidT "" p
            ps <- ioToIORes (proveTheory lidT p' thName (Theory sign'' (toThSens sens'')))
            -- update the development graph
            -- todo: throw out the stuff about edges
            -- instead, mark proven things as proven in the node
            let newThms = filter isProvedStat ps
                (nextDGraph, nextHistoryElem) = 
                 if null newThms then (dGraph, ([], []))
                 else let 
                     oldNode@(_,oldContents) = labNode' (safeContext 
                        "Proofs.InferBasic.basicInferenceNode"  dGraph node)
                     newTh = case (dgn_theory oldContents) of
                             G_theory lid sig sens ->
                               G_theory lid sig (markProved (Comorphism cid) 
                                                            lidT newThms sens)
                     n = getNewNode dGraph
                     newNode = (n, oldContents{dgn_theory = newTh})
                     (newGraph,changes) =
                             adoptEdges (insNode newNode $ dGraph) node n
                     newGraph' = delNode node $ newGraph
                     newChanges = InsertNode newNode : changes ++ 
                                        [DeleteNode oldNode]
                     rules = map (\s -> BasicInference (Comorphism cid) 
                                            (BasicProof lidT s)) 
                                 ps
                     in (newGraph',(rules,newChanges))
            return $ mkResultProofStatus proofStatus nextDGraph nextHistoryElem

-- | mark all newly proven goals with their proof tree
markProved :: (Ord a, Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree) => 
     AnyComorphism -> lid -> [Proof_status proof_tree] -> ThSens a (AnyComorphism,BasicProof) -> ThSens a (AnyComorphism,BasicProof)
markProved c lid status = 
 OMap.mapWithKey $ \ name senStat -> 
  let findProof [] = senStat
      findProof (s:rest) =
       if goalName s == name 
        then senStat { thmStatus = (c, BasicProof lid s) : thmStatus senStat }
        else findProof rest
   in findProof status

