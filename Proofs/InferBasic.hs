{-| 
   
Module      :  $Header$
Copyright   :  (c) Jorina F. Gerken, Till Mossakowski, Uni Bremen 2002-2004
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
import Common.AS_Annotation
import Data.Graph.Inductive.Graph
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Id
import Common.AS_Annotation
import Syntax.AS_Library
import Syntax.Print_AS_Library()
import Proofs.Proofs
import Proofs.EdgeUtils
import Proofs.StatusUtils
import Proofs.Global
import Proofs.Local
import Proofs.HideTheoremShift
import Proofs.TheoremHideShift
import GUI.Utils

{- todo: implement apply for GlobDecomp and Subsumption 
   the list of DGChage must be constructed in parallel to the
   new DGraph -}
applyRule :: DGRule -> DGraph -> Maybe ([DGChange],DGraph)
applyRule = error "Proofs.hs:applyRule"


{- automatically applies all rules to the library
   denoted by the library name of the given proofstatus-}
automatic :: ProofStatus -> IO ProofStatus
automatic = automaticRecursive 0


{- applies the rules recursively until no further changes can be made -}
automaticRecursive :: Int -> ProofStatus -> IO ProofStatus
automaticRecursive cnt proofstatus = do
  auxProofstatus@(ln, libEnv, historyMap) <- automaticApplyRules proofstatus
  finalProofstatus <- mergeHistories cnt auxProofstatus
  case finalProofstatus of
    Nothing -> return proofstatus
    Just p -> automaticRecursive 1 p


{- sequentially applies all rules to the given proofstatus,
   ie to the library denoted by the library name of the proofstatus -}
automaticApplyRules :: ProofStatus -> IO ProofStatus
automaticApplyRules p = do
--  p0 <- theoremHideShift p
  p1 <- globSubsume p --p0
  p2 <- globDecomp p1
  p3 <- locSubsume p2
  p4 <- locDecomp p3
  hideTheoremShift True p4


{- merges for every library the new history elements
   to one new history element -}
mergeHistories :: Int -> ProofStatus -> IO (Maybe ProofStatus)
mergeHistories cnt proofstatus@(ln,libEnv,_) = do
  (numChanges,newProofstatus) <- mergeHistoriesAux cnt (libNames) proofstatus
  if (numChanges > 0) then 
     return (Just (changeCurrentLibName ln newProofstatus))
    else return Nothing

  where
    libNames = Map.keys libEnv


{- auxiliary method for mergeHistories:
   determined the library names and recursively applies mergeHistory -}
mergeHistoriesAux :: Int -> [LIB_NAME] -> ProofStatus -> IO (Int,ProofStatus)
mergeHistoriesAux cnt [] proofstatus = return (0,proofstatus)
mergeHistoriesAux cnt (ln:list) proofstatus = do
  ps <- mergeHistory cnt (changeCurrentLibName ln proofstatus)
  case ps of
    Just newProofstatus -> do 
      (i,finalProofstatus) <- mergeHistoriesAux cnt list newProofstatus
      return (i+1,finalProofstatus)
    Nothing -> mergeHistoriesAux cnt list proofstatus


{- merges the new history elements of a single library
   to one new history elemebt-}
mergeHistory :: Int -> ProofStatus -> IO (Maybe ProofStatus)
mergeHistory cnt proofstatus@(ln,libEnv,historyMap) = do
  let history = lookupHistory ln proofstatus
      dgraph = lookupDGraph ln proofstatus
  let (newHistoryPart, oldHistory) = splitAt (5+cnt) history
  if (null (concat (map snd (take 5 newHistoryPart)))) && (cnt == 1) then
     return Nothing
   else do
    let (rules, changes) = concatHistoryElems (reverse newHistoryPart)
	newHistoryElem = (rules, removeContraryChanges changes)
	newHistory = newHistoryElem:oldHistory
    return (Just (ln,libEnv,Map.insert ln newHistory historyMap))


{- concats the given history elements to one history element-}
concatHistoryElems :: [([DGRule],[DGChange])] -> ([DGRule],[DGChange])
concatHistoryElems [] = ([],[])
concatHistoryElems ((rules,changes):elems) =
  (rules++(fst (concatHistoryElems elems)),changes++(snd (concatHistoryElems elems)))

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
selectProver provers = do
   sel <- ioToIORes $ listBox 
                "Choose a translation to a prover-supported logic"
                (map (show.snd) provers)
   i <- case sel of
           Just j -> return j
           _ -> resToIORes $ fatal_error "Proofs.Proofs: selection" nullRange
   return (provers!!i)
 
cons_check :: Logic lid sublogics
              basic_spec sentence symb_items symb_map_items
              sign morphism symbol raw_symbol proof_tree 
           => lid -> ConsChecker sign sentence morphism proof_tree 
           -> String -> TheoryMorphism sign sentence morphism 
           -> IO([Proof_status proof_tree])
cons_check _ = prove

proveTheory :: Logic lid sublogics
              basic_spec sentence symb_items symb_map_items
              sign morphism symbol raw_symbol proof_tree 
           => lid -> Prover sign sentence proof_tree 
           -> String -> Theory sign sentence -> IO([Proof_status proof_tree])
proveTheory _ = prove

-- applies basic inference to a given node
basicInferenceNode :: Bool -> LogicGraph -> (LIB_NAME,Node) -> ProofStatus 
                          -> IO (Result ProofStatus)
basicInferenceNode checkCons lg (ln, node)
         proofStatus@(libname,libEnv,proofHistory) = do
      let dGraph = lookupDGraph libname proofStatus
      ioresToIO $ do 
        -- compute the theory of the node, and its name
        G_theory lid1 sign axs <- 
             resToIORes $ computeTheory libEnv (ln, node)
        ctx <- resToIORes 
                    $ maybeToMonad ("Could node find node "++show node)
                    $ fst $ match node dGraph
        let nlab = lab' ctx  
            nodeName = case nlab of
              DGNode _ _ _ _ _ _ _-> dgn_name nlab
              DGRef _ _ _ _ _ -> dgn_renamed nlab
            thName = showPretty (getLIB_ID ln) "_"
                     ++ {-maybe (show node)-} showName nodeName
        -- compute the list of proof goals
            -- workaround for Klaus' problem; Till
        let inEdges = inn dGraph node
            localEdges = filter isUnprovenLocalThm inEdges
        goalslist <- if checkCons then return []
                      else resToIORes $ mapM (getGoals libEnv ln) localEdges
        G_theory lid3 _ goals <- case goalslist of 
            [] -> return $ G_theory lid1 sign noSens 
            hd : tl -> flatG_sentences hd tl
        goals1 <- coerceThSens lid3 lid1 "" goals
        -- select a suitable translation and prover
        let cms = findComorphismPaths lg $ sublogicOfTh $ G_theory lid1 sign
                          $ Set.union axs goals1
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
                                       t_target = Theory sign'' sens'',
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
            let lidT = targetLogic cid
                transTh = resToIORes . map_theory cid
            bTh' <- coerceBasicTheory lid1 (sourceLogic cid) "" 
                   (sign, toNamedList axs ++ map markGoal (toNamedList goals1))
            (sign'',sens'') <- transTh bTh'
            -- call the prover
            p' <- coerceProver lid4 lidT "" p
            ps <- ioToIORes (proveTheory lidT p' thName (Theory sign'' sens''))
            -- update the development graph
            let (nextDGraph, nextHistoryElem) = 
                          proveLocalEdges dGraph localEdges
	        newProofStatus
		 = mkResultProofStatus proofStatus nextDGraph nextHistoryElem
            return newProofStatus

proveLocalEdges :: DGraph -> [LEdge DGLinkLab] -> (DGraph,([DGRule],[DGChange]))
proveLocalEdges dGraph edges = (nextDGraph,([LocalInference],changes))

  where (nextDGraph,(_,changes)) = proveLocalEdgesAux ([],[]) dGraph edges


proveLocalEdgesAux :: ([DGRule],[DGChange]) -> DGraph -> [LEdge DGLinkLab] 
  -> (DGraph,([DGRule],[DGChange]))
proveLocalEdgesAux historyElem dGraph [] = (dGraph, historyElem)
proveLocalEdgesAux (rules,changes) dGraph ((edge@(src, tgt, edgelab)):edges) = 
  if True then proveLocalEdgesAux (rules,(DeleteEdge edge):((InsertEdge provenEdge):changes)) (insEdge provenEdge(delLEdge edge dGraph)) edges
   else proveLocalEdgesAux (rules,changes) dGraph edges

  where
    morphism = dgl_morphism edgelab
    (LocalThm _ conservativity conservStatus) = (dgl_type edgelab)
    proofBasis = [] -- to be implemented
    provenEdge = (src,
	       tgt,
	       DGLink {dgl_morphism = morphism,
		       dgl_type = 
		         (LocalThm (Proven LocalInference proofBasis)
			  conservativity conservStatus),
		       dgl_origin = DGProof}
               )
