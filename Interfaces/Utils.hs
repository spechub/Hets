{-# LANGUAGE CPP #-}
{- |
Module      :$Header$
Description : utilitary functions
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

Interfaces.Utils contains different utilitary functions for the
abstract interface

-}

module Interfaces.Utils
         ( getAllNodes
         , getAllEdges
         , initNodeInfo
         , emptyIntIState
         , emptyIntState
         , wasProved
         , parseTimeLimit
         , addCommandHistoryToState
         , checkConservativityNode
         , checkConservativityEdge
         , updateNodeProof
         ) where

import Interfaces.Command
import Interfaces.DataTypes
import Interfaces.GenericATPState
import qualified Interfaces.Command as IC
import Interfaces.History

import Data.Graph.Inductive.Graph
import Data.Maybe (fromMaybe)
import Data.List (isPrefixOf, stripPrefix, nubBy)
import Data.IORef
import Data.Map (insert)

import Static.DevGraph
import Static.GTheory
import Static.History
import Static.ComputeTheory

import Proofs.AbstractState

import Driver.Options (rmSuffix)
import System.Directory (getCurrentDirectory)

import Logic.Comorphism
import Logic.Prover
import Logic.Logic
import Logic.Grothendieck
import Logic.Coerce
import Comorphisms.LogicGraph(logicGraph)

import qualified Data.Map as Map
import qualified Common.OrderedMap as OMap
import Common.Utils (splitOn)
import Common.Result
import Common.LibName
import qualified Common.Lib.SizedList as SizedList
import Common.Consistency
import Common.ExtSign
import Common.AS_Annotation (SenAttr(..), makeNamed, mapNamed)
import qualified Common.Doc as Pretty

#ifdef UNI_PACKAGE
import GUI.Utils
#endif

-- | Returns the list of all nodes, if it is not up to date
-- the function recomputes the list
getAllNodes :: IntIState  -> [LNode DGNodeLab]
getAllNodes st
 = labNodesDG $ lookupDGraph (i_ln st) (i_libEnv st)

-- | Returns the list of all edges, if it is not up to date
-- the funcrion recomputes the list
getAllEdges :: IntIState -> [LEdge DGLinkLab]
getAllEdges st = labEdgesDG $ lookupDGraph (i_ln st) (i_libEnv st)

-- | Constructor for CMDLProofGUIState datatype
initNodeInfo:: (Logic lid1 sublogics1
         basic_spec1 sentence1 symb_items1 symb_map_items1
         sign1 morphism1 symbol1 raw_symbol1 proof_tree1) =>
         ProofState lid1 sentence1 -> Int
         -> Int_NodeInfo
initNodeInfo = Element

emptyIntIState :: LibEnv -> LibName -> IntIState
emptyIntIState le ln =
  IntIState {
    i_libEnv = le,
    i_ln  = ln,
    elements = [],
    cComorphism = Nothing,
    prover = Nothing,
    consChecker = Nothing,
    save2file = False,
    useTheorems = False,
    script = ATPTacticScript {
                 tsTimeLimit = 20,
                 tsExtraOpts = [] },
    loadScript = False
    }

emptyIntState :: IntState
emptyIntState =
    IntState { i_state = Just $ emptyIntIState emptyLibEnv $ emptyLibName ""
             , i_hist  = IntHistory { undoList = []
                                    , redoList = [] }
             , filename = []
             }

-- If an absolute path is given,
-- it tries to remove the current working directory as prefix of it.
tryRemoveAbsolutePathComponent :: String -> IO String
tryRemoveAbsolutePathComponent f
   | "/" `isPrefixOf` f = do
                           dir <- getCurrentDirectory
                           return $ fromMaybe f (stripPrefix (dir ++ "/") f)
   | otherwise        = return f

-- Converts a list of proof-trees to a prove
proofTreeToProve :: FilePath
     -> ProofState lid sentence -- current proofstate
     -> Maybe (G_prover, AnyComorphism)     -- possible used translation
     -> [ProofStatus proof_tree]           -- goals included in prove
     -> [IC.Command]
proofTreeToProve fn st pcm pt =
    [ IC.SelectCmd IC.Node nodeName, IC.GlobCmd IC.DropTranslation ]
    ++ maybe [] (\ (Comorphism cid) -> map (IC.SelectCmd
                IC.ComorphismTranslation) $
                drop 1 $ splitOn ';' $ language_name cid) trans
    ++ maybe [] (( : []) . IC.SelectCmd IC.Prover) prvr
    ++ concatMap goalToCommands goals
    where
      -- selected prover
      prvr = maybe (selectedProver st) (Just . getProverName . fst) pcm
      -- selected translation
      trans = maybe Nothing (Just . snd) pcm
      -- 1. filter out the not proven goals
      -- 2. reverse the list, because the last proven goals are on top
      -- 3. convert all proof-trees to goals
      -- 4. merge goals with same used axioms
      goals = mergeGoals $ Prelude.reverse
                  $ Prelude.map (\ x -> (goalName x, parseTimeLimit x))
                  $ Prelude.filter wasProved pt
      -- axioms to include in prove
      allax = case theory st of G_theory _ _ _ axs _ -> OMap.keys axs
      nodeName = dropName fn $ theoryName st
      -- A goal is a pair of a name as String and time limit as Int
      goalToCommands :: (String, Int) -> [IC.Command]
      goalToCommands (n, t) =
          [ IC.SelectCmd IC.Goal n, IC.SetAxioms allax, IC.TimeLimit t,
            IC.GlobCmd IC.ProveCurrent ]

-- Merge goals with the same time-limit
mergeGoals :: [(String, Int)] -> [(String, Int)]
mergeGoals []     = []
mergeGoals (h:[]) = [h]
mergeGoals ((n,l):t)  | l == l' = mergeGoals $ (n ++ ' ':n', l):Prelude.tail t
                      | otherwise = (n,l):mergeGoals t
    where
        (n',l') = Prelude.head t

dropName :: String -> String -> String
dropName fch s = maybe s Prelude.tail (stripPrefix fch s)

-- This checks wether a goal was proved or not
wasProved :: ProofStatus proof_Tree -> Bool
wasProved g = case goalStatus g of
    Proved _  -> True
    _         -> False

-- Converts a proof-tree into a goal.
parseTimeLimit :: ProofStatus proof_tree -> Int
parseTimeLimit pt =
  if Prelude.null lns then 20 else read $ Prelude.drop (length tlStr) $ last lns
  where
    (TacticScript scrpt) = tacticScript pt
    lns = Prelude.filter (isPrefixOf tlStr) $ splitOn '\n' scrpt
    tlStr = "Time limit: "

addCommandHistoryToState :: IORef IntState
    -> ProofState lid sentence         -- current proofstate
    -> Maybe (G_prover, AnyComorphism) -- possible used translation
    -> [ProofStatus proof_tree]       -- goals included in prove
    -> IO (Result ())
addCommandHistoryToState intSt st pcm pt
    | null $ filter wasProved pt = return $ Result [] $ Just ()
    | otherwise = do
        ost <- readIORef intSt
        fn <- tryRemoveAbsolutePathComponent $ filename ost
        writeIORef intSt $ add2history
           (IC.GroupCmd $ proofTreeToProve (rmSuffix fn) st pcm pt)
           ost [ IStateChange $ i_state ost ]
        return $ Result [] $ Just ()


conservativityRule :: DGRule
conservativityRule = DGRule "ConservativityCheck"

conservativityChoser :: Bool -> [ConservativityChecker sign sentence morphism]
  -> IO (Result (ConservativityChecker sign sentence morphism))
#ifdef UNI_PACKAGE
conservativityChoser useGUI checkers = case checkers of
  [] -> return $ fail "No conservativity checker available"
  hd : tl ->
    if useGUI && not (null tl) then do
      chosenOne <- listBox "Pic a conservativity checker"
                                $ Prelude.map checkerId checkers
      case chosenOne of
        Nothing -> return $ fail "No conservativity checker chosen"
        Just i -> return $ return $ checkers !! i
   else
#else
conservativityChoser _ checkers = case checkers of
  [] -> return $ fail "No conservativity checker available"
  hd : _ ->
#endif
   return $ return hd

checkConservativityNode :: Bool -> (LNode DGNodeLab) -> LibEnv -> LibName
                        -> IO (String, LibEnv, ProofHistory)
checkConservativityNode useGUI (nodeId, nodeLab) libEnv ln = do
  let dg = lookupDGraph ln libEnv
      emptyTh = case dgn_sign nodeLab of
        G_sign lid _ _ ->
            noSensGTheory lid (mkExtSign $ empty_signature lid) startSigId
      newN = getNewNodeDG dg
      newL = (newNodeLab emptyNodeName DGProof emptyTh)
             { globalTheory = Just emptyTh }
      morphism = case resultToMaybe $ ginclusion logicGraph (dgn_sign newL) $
                   dgn_sign nodeLab of
             Just m  -> m
             Nothing -> error "Utils.checkConservativityNode"
      lnk = (newN, nodeId, defDGLink
        morphism (ScopedLink Global DefLink $ getNodeConsStatus nodeLab)
        SeeSource)
      (tmpDG, _) = updateDGOnly dg $ InsertNode (newN, newL)
      (tempDG, InsertEdge lnk') = updateDGOnly tmpDG $ InsertEdge lnk
      tempLibEnv = insert ln tempDG libEnv
  (str, _, (_,_,lnkLab),_) <- checkConservativityEdge useGUI lnk' tempLibEnv ln
  if isPrefixOf "No conservativity" str
    then return (str, libEnv, SizedList.empty)
    else do
         let nInfo = nodeInfo nodeLab
             nodeLab' = nodeLab { nodeInfo = nInfo { node_cons_status =
                          getLinkConsStatus $ dgl_type lnkLab } }
             changes = [ SetNodeLab nodeLab (nodeId, nodeLab') ]
             dg' = changesDGH dg changes
             history = snd $ splitHistory dg dg'
             libEnv' = insert ln (groupHistory dg conservativityRule dg') libEnv
         return (str, libEnv', history)

checkConservativityEdge :: Bool -> (LEdge DGLinkLab) -> LibEnv -> LibName
                        -> IO (String, LibEnv, LEdge DGLinkLab, ProofHistory)
checkConservativityEdge useGUI link@(source,target,linklab) libEnv ln
 = do
    let thT =
         case computeTheory libEnv ln target of
          Result _ (Just th1) -> th1
          _ -> error "checkconservativityOfEdge: computeTheory"
    G_theory lidT _ _ sensT _ <- return thT
    GMorphism cid _ _ morphism _ <- return $ dgl_morphism linklab
    morphism' <- coerceMorphism (targetLogic cid) lidT
                 "checkconservativityOfEdge" morphism
    let compMor = case dgn_sigma $ labDG (lookupDGraph ln libEnv) target of
          Nothing -> morphism'
          Just (GMorphism cid' _ _ morphism2 _) -> case
            coerceMorphism (targetLogic cid') lidT
                   "checkconservativityOfEdge" morphism2
               >>= comp morphism' of
                 Result _ (Just phi) -> phi
                 _ -> error "checkconservativityOfEdge: comp"
    let thS =
         case computeTheory libEnv ln source of
           Result _ (Just th1) -> th1
           _ -> error "checkconservativityOfEdge: computeTheory"
    G_theory lidS signS _ sensS _ <- return thS
    case coerceSign lidS lidT "checkconservativityOfEdge.coerceSign" signS of
     Nothing -> return ( "no implementation for heterogeneous links"
                       , libEnv, link, SizedList.empty)
     Just signS' -> do
      sensS' <- coerceThSens lidS lidT "checkconservativityOfEdge1" sensS
      let transSensSrc = propagateErrors
           $ mapThSensValueM (map_sen lidT compMor) sensS'
      if length (conservativityCheck lidT) < 1
          then return ("No conservativity checkers available",
                       libEnv, link, SizedList.empty)
          else
           do
            checkerR <- conservativityChoser useGUI $ conservativityCheck lidT
            if hasErrors $ diags checkerR
             then return ("No conservativity checker chosen",
                          libEnv, link, SizedList.empty)
             else
              do
               let chCons = checkConservativity $
                            fromMaybe (error "checkconservativityOfEdge")
                               $ maybeResult checkerR
                   inputThSens = nubBy (\ a b -> sentence a == sentence b) $
                                 toNamedList $
                                 sensT `OMap.difference` transSensSrc
               Result ds res <-
                       chCons
                          (plainSign signS', toNamedList sensS')
                          compMor inputThSens
               let consShow = case res of
                              Just (Just (cst, _)) -> cst
                              _                    -> Unknown "Unknown"
                   cs' = consShow
                   consNew csv = if cs' >= csv
                              then Proven conservativityRule emptyProofBasis
                              else LeftOpen
                   (newDglType, edgeChange) = case dgl_type linklab of
                     ScopedLink sc dl (ConsStatus consv cs op) ->
                       let np = consNew consv in
                       (ScopedLink sc dl $
                        ConsStatus consv (max cs $ max consv cs') np, np /= op)
                     t -> (t, False)
                   provenEdge = ( source
                                , target
                                , linklab { dgl_type = newDglType }
                                )
                   dg = lookupDGraph ln libEnv
                   nodelab = labDG dg target
                   obligations = case res of
                        Just (Just (_, os)) -> os
                        _                   -> []
                   namedNewSens = toThSens [(makeNamed "" o) {isAxiom = False} |
                                             o<-obligations]
               G_theory glid gsign gsigid gsens gid <- return $ dgn_theory
                                                                  nodelab
               namedNewSens' <- coerceThSens lidT glid "" namedNewSens
               let oldSens = OMap.toList gsens
                   -- Sort out the named sentences which have a different name,
                   -- but same sentence
                   mergedSens = nubBy (\(_,a) (_,b) -> sentence a == sentence b)
                                $ oldSens ++ OMap.toList namedNewSens'
                   (newTheory, nodeChange) =
                     (G_theory glid gsign gsigid (OMap.fromList mergedSens) gid,
                      length oldSens /= length mergedSens)
                   newTargetNode = (target
                                   ,nodelab { dgn_theory = newTheory })
                   nodeChanges = [SetNodeLab nodelab newTargetNode | nodeChange]
                   edgeChanges = if edgeChange then
                            [ DeleteEdge (source,target,linklab)
                            , InsertEdge provenEdge ] else []
                   nextGr = changesDGH dg $ nodeChanges ++ edgeChanges
                   newLibEnv = insert ln
                     (groupHistory dg conservativityRule nextGr) libEnv
                   history = snd $ splitHistory dg nextGr
                   sig1 = case gsign of
                               ExtSign s1 _ -> s1
                   showObls [] = ""
                   showObls lst = ", provided that the following proof "
                                 ++ "obligations can be discharged:\n"
                                 ++ show (Pretty.vsep $ map (print_named glid .
                                     mapNamed (simplify_sen glid sig1)) lst)
                   showRes = case res of
                             Just (Just (cst,_)) -> "The link is "
                              ++ showConsistencyStatus cst
                              ++ showObls (toNamedList namedNewSens')
                             _ -> "Could not determine whether link is "
                                   ++ "conservative"
                   myDiags = showRelDiags 2 ds
               return ( showRes ++ "\n" ++ myDiags
                      , newLibEnv, provenEdge, history)

updateNodeProof :: LibName -> IntState -> LNode DGNodeLab
                -> Maybe G_theory -> (IntState, Maybe [DGChange])
updateNodeProof ln ost (v, dgnode) tres = case tres of
  Just thry ->
    case i_state ost of
      Nothing -> (ost, Nothing)
      Just iist ->
        let le = i_libEnv iist
            dg = lookupDGraph ln le
            nn = getDGNodeName dgnode
            new = dgnode { dgn_theory = thry }
            l = new { globalTheory = computeLabelTheory le dg (v, new) }
            newDg0 = changeDGH dg $ SetNodeLab dgnode (v, l)
            newDG1 = togglePending newDg0 $ changedLocalTheorems newDg0 (v, l)
            newDG2 = togglePending newDG1 $ changedPendingEdges newDG1
            newDg = groupHistory dg (DGRule "Node proof") newDG2
            history = reverse $ flatHistory $ snd $ splitHistory dg newDg
            nst = add2history
                    (CommentCmd $ "basic inference done on " ++ nn ++ "\n")
                    ost $ [DgCommandChange ln]
            nwst = nst { i_state =
                           Just iist { i_libEnv = Map.insert ln newDg le } }
        in (nwst, Just history)
  Nothing -> (ost, Nothing)
