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

module Proofs.InferBasic
  ( basicInferenceNode
  , consistencyCheck
  , SType (..)
  , ConsistencyStatus (..)
  ) where

import Static.GTheory
import Static.DevGraph
import Static.ComputeTheory

import Proofs.EdgeUtils
import Proofs.AbstractState

import Common.DocUtils (showDoc)
import Common.ExtSign
import Common.LibName
import Common.Result
import Common.ResultT
import Common.AS_Annotation
import qualified Common.Lib.Graph as Tree

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
import Data.Graph.Inductive.Basic (elfilter)
import Data.Graph.Inductive.Graph
import Data.Maybe
import Data.Time.LocalTime (timeToTimeOfDay)
import Data.Time.Clock (secondsToDiffTime)
import Data.Ord (comparing)

import Control.Monad.Trans

import System.Timeout

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
   lid -> LibEnv -> LibName -> DGraph -> [LEdge DGLinkLab]
   -> Maybe (FreeDefMorphism sentence morphism)
getFreeDefMorphism lid libEnv ln dg path = case path of
  [] -> error "getFreeDefMorphism"
  (s, t, l) : rp -> do
    gmor@(GMorphism cid _ _ fmor _) <- return $ dgl_morphism l
    G_theory lidth (ExtSign _sign _) _ axs _ <-
      computeTheory libEnv ln s
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
   lid -> LibEnv -> LibName -> DGraph -> Node
   -> [FreeDefMorphism sentence morphism]
getCFreeDefMorphs lid libEnv ln dg node = let
  (frees, cofrees) = getCFreeDefLinks dg node
  myget = mapMaybe (getFreeDefMorphism lid libEnv ln dg)
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
    -- compute the theory of the node, and its name
    -- may contain proved theorems
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

data SType = CSUnchecked
           | CSTimeout
           | CSError
           | CSInconsistent
           | CSConsistent
           deriving (Eq, Ord)

data ConsistencyStatus = ConsistencyStatus { sType :: SType
                                           , sMessage :: String }

instance Show ConsistencyStatus where
  show cs = case sType cs of
    CSUnchecked -> "Unchecked"
    _ -> sMessage cs

instance Eq ConsistencyStatus where
  (==) cs1 cs2 = compare cs1 cs2 == EQ

instance Ord ConsistencyStatus where
  compare = comparing sType

consistencyCheck :: Bool -> G_cons_checker -> AnyComorphism -> LibName -> LibEnv
                 -> DGraph -> LNode DGNodeLab -> Int -> IO ConsistencyStatus
consistencyCheck includeTheorems (G_cons_checker lid4 cc) (Comorphism cid) ln
  le dg (n', lbl) t'' = do
  let lidS = sourceLogic cid
      lidT = targetLogic cid
      thName = shows (getLibId ln) "_" ++ getDGNodeName lbl
      t = t'' * 1000000
      t' = timeToTimeOfDay $ secondsToDiffTime $ toInteger t''
      ts = TacticScript $ if ccNeedsTimer cc then "" else show t''
      mTimeout = "No results within: " ++ show t'
  case do
        (G_theory lid1 (ExtSign sign _) _ axs _) <- getGlobalTheory lbl
        let namedSens = toNamedList axs
            sens = if includeTheorems then
              map (\ s -> s { isAxiom = True }) namedSens
              else namedSens
        bTh'@(sig1, _) <- coerceBasicTheory lid1 lidS "" (sign, sens)
        (sig2, sens2) <- wrapMapTheory cid bTh'
        incl <- subsig_inclusion lidT (empty_signature lidT) sig2
        return (sig1, TheoryMorphism
          { tSource = emptyTheory lidT
          , tTarget = Theory sig2 $ toThSens sens2
          , tMorphism = incl }) of
    Result ds Nothing ->
      return $ ConsistencyStatus CSError $ unlines $ map diagString ds
    Result _ (Just (sig1, mor)) -> do
      cc' <- coerceConsChecker lid4 lidT "" cc
      ret <- (if ccNeedsTimer cc then timeout t else ((return . Just) =<<))
        (ccAutomatic cc' thName ts mor $ getCFreeDefMorphs lidT le ln dg n')
      return $ case ret of
        Just ccStatus -> case ccResult ccStatus of
          Just b -> if b then let
            Result ds ms = extractModel cid sig1 $ ccProofTree ccStatus
            msgLines = map diagString ds ++ lines (show $ ccProofTree ccStatus)
            in case ms of
            Nothing -> ConsistencyStatus CSConsistent $ unlines
              ("consistent, but could not reconstruct a model" : msgLines)
            Just (sig3, sens3) -> let
              thTxt = showDoc
                (G_theory lidS (mkExtSign sig3) startSigId (toThSens sens3)
                        startThId) ""
              in ConsistencyStatus CSConsistent $
                 case filterDiags 2 ds of
                   [] -> thTxt
                   _ -> unlines $ lines thTxt ++ "%[" : msgLines ++ ["]%"]
            else ConsistencyStatus CSInconsistent $ show (ccProofTree ccStatus)
          Nothing -> if ccUsedTime ccStatus >= t' then
            ConsistencyStatus CSTimeout mTimeout
            else ConsistencyStatus CSError $ show (ccProofTree ccStatus)
        Nothing -> ConsistencyStatus CSTimeout mTimeout

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
