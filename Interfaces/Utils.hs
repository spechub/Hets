{-# LANGUAGE CPP, RecordWildCards #-}

{- |
Module      :./Interfaces/Utils.hs
Description : utilitary functions
Copyright   : uni-bremen and DFKI
License     : GPLv2 or higher, see LICENSE.txt
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
         , checkConservativityEdgeWith
         , recordConservativityResult
         , getUsableConservativityCheckers
         , updateNodeProof
         ) where

import Interfaces.Command ( Command(CommentCmd) )
import Interfaces.DataTypes
import Interfaces.GenericATPState
import qualified Interfaces.Command as IC
import Interfaces.History

import Control.Monad (unless, filterM)

import Data.Graph.Inductive.Graph
import Data.Maybe (isNothing)
import Data.List
import Data.IORef

import Static.DevGraph
import Static.DgUtils
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
import Comorphisms.LogicGraph (logicGraph)

import qualified Data.Map as Map
import qualified Data.Set as Set
import Common.IRI
import Common.Result
import Common.LibName
import qualified Common.Lib.SizedList as SizedList
import Common.Consistency
import Common.ExtSign
import Common.AS_Annotation (SenAttr (..), makeNamed, mapNamed)
import qualified Common.Doc as Pretty
import Common.Utils
import qualified Control.Monad.Fail as Fail
import Common.ResultT (ResultT(runResultT, ResultT))

#ifdef UNI_PACKAGE
import GUI.Utils
#endif

{- | Returns the list of all nodes, if it is not up to date
the function recomputes the list -}
getAllNodes :: IntIState -> [LNode DGNodeLab]
getAllNodes st
 = labNodesDG $ lookupDGraph (i_ln st) (i_libEnv st)

{- | Returns the list of all edges, if it is not up to date
the funcrion recomputes the list -}
getAllEdges :: IntIState -> [LEdge DGLinkLab]
getAllEdges st = labEdgesDG $ lookupDGraph (i_ln st) (i_libEnv st)

-- | Constructor for CMDLProofGUIState datatype
initNodeInfo :: ProofState -> Int -> Int_NodeInfo
initNodeInfo = Element

emptyIntIState :: LibEnv -> LibName -> IntIState
emptyIntIState le ln =
  IntIState {
    i_libEnv = le,
    i_ln = ln,
    elements = [],
    cComorphism = Nothing,
    prover = Nothing,
    consChecker = Nothing,
    save2file = False,
    useTheorems = False,
    showOutput = False,
    script = ATPTacticScript {
                 tsTimeLimit = 20,
                 tsExtraOpts = [] },
    loadScript = False
    }

emptyIntState :: IntState
emptyIntState =
    IntState { i_state = Just $ emptyIntIState emptyLibEnv $ iriLibName nullIRI
             , i_hist = IntHistory { undoList = []
                                    , redoList = [] }
             , filename = []
             }

{- If an absolute path is given,
it tries to remove the current working directory as prefix of it. -}
tryRemoveAbsolutePathComponent :: String -> IO String
tryRemoveAbsolutePathComponent f
   | "/" `isPrefixOf` f = do
                           dir <- getCurrentDirectory
                           return $ tryToStripPrefix (dir ++ "/") f
   | otherwise = return f

-- Converts a list of proof-trees to a prove
proofTreeToProve :: FilePath
     -> ProofState                         -- current proofstate
     -> Maybe (G_prover, AnyComorphism)    -- possible used translation
     -> [ProofStatus proof_tree]           -- goals included in prove
     -> String
     -> (Bool, Int)
     -> [IC.Command]
proofTreeToProve fn st pcm pt nodeName (useTm, tm) =
    [ IC.SelectCmd IC.Node nodeName', IC.GlobCmd IC.DropTranslation ]
    ++ maybe [] (\ (Comorphism cid) -> map
                 (IC.SelectCmd IC.ComorphismTranslation)
                 (drop 1 $ splitOn ';' $ language_name cid)) commorf
    ++ maybe [] ((: []) . IC.SelectCmd IC.Prover) prvr
    ++ concatMap goalToCommands goals
    where
      -- selected prover
      prvr = maybe (selectedProver st) (Just . getProverName . fst) pcm
      -- selected translation
      commorf = case selectedProver st of
          Nothing -> Nothing
          Just theProver ->
            case Map.lookup theProver $ proversMap st of
              Nothing -> Nothing
              Just com -> Just $ head com
      {- 1. filter out the not proven goals
      2. reverse the list, because the last proven goals are on top
      3. convert all proof-trees to goals
      4. merge goals with same used axioms -}
      goals = mergeGoals $ reverse
                  $ map (\ x -> (goalName x, parseTimeLimit x))
                  $ filter wasProved pt
      -- axioms to include in prove
      allax = map fst $ getAxioms st
      nodeName' = if nodeName == "" then dropName fn $ theoryName st
                                    else nodeName
      -- A goal is a pair of a name as String and time limit as Int
      goalToCommands :: (String, Int) -> [IC.Command]
      goalToCommands (n, t) =
          [ IC.SelectCmd IC.Goal n
          , IC.SetAxioms allax
          , IC.TimeLimit (if useTm then tm else t)
          , IC.GlobCmd IC.ProveCurrent]

-- Merge goals with the same time-limit
mergeGoals :: [(String, Int)] -> [(String, Int)]
mergeGoals i = case i of
  (n, l) : t@((n', l') : tl) ->
    if l == l' then mergeGoals $ (n ++ ' ' : n', l) : tl
    else (n, l) : mergeGoals t
  _ -> i

dropName :: String -> String -> String
dropName fch s = maybe s tail (stripPrefix fch s)

-- This checks wether a goal was proved or not
wasProved :: ProofStatus proof_Tree -> Bool
wasProved g = case goalStatus g of
    Proved _ -> True
    _ -> False

-- Converts a proof-tree into a goal.
parseTimeLimit :: ProofStatus proof_tree -> Int
parseTimeLimit pt =
  if null lns then 20 else read $ drop (length tlStr) $ last lns
  where
    TacticScript scrpt = tacticScript pt
    lns = filter (isPrefixOf tlStr) $ splitOn '\n' scrpt
    tlStr = "Time limit: "

addCommandHistoryToState :: IORef IntState
    -> ProofState                    -- current proofstate
    -> Maybe (G_prover, AnyComorphism) -- possible used translation
    -> [ProofStatus proof_tree]       -- goals included in prove
    -> String
    -> (Bool, Int)
    -> IO ()
addCommandHistoryToState intSt st pcm pt str (useTm, timeout) =
  unless (not $ any wasProved pt) $ do
        ost <- readIORef intSt
        fn <- tryRemoveAbsolutePathComponent $ filename ost
        writeIORef intSt $ add2history
           (IC.GroupCmd $ proofTreeToProve (rmSuffix fn) st pcm pt str
            (useTm, timeout)) ost [IStateChange $ i_state ost]

conservativityRule :: DGRule
conservativityRule = DGRule "ConservativityCheck"

conservativityChoser :: Bool -> [ConservativityChecker sign sentence morphism]
  -> IO (Result (ConservativityChecker sign sentence morphism))
#ifdef UNI_PACKAGE
conservativityChoser useGUI checkers = case checkers of
  [] -> return $ Fail.fail "No conservativity checker available"
  hd : tl ->
    if useGUI && not (null tl) then do
      chosenOne <- listBox "Pick a conservativity checker"
                                $ map checkerId checkers
      case chosenOne of
        Nothing -> return $ Fail.fail "No conservativity checker chosen"
        Just i -> return $ return $ checkers !! i
   else
#else
conservativityChoser _ checkers = case checkers of
  [] -> return $ Fail.fail "No conservativity checker available"
  hd : _ ->
#endif
   return $ return hd

checkConservativityNode :: Bool -> LNode DGNodeLab -> LibEnv -> LibName
  -> IO (String, LibEnv, ProofHistory)
checkConservativityNode useGUI (nodeId, nodeLab) libEnv ln = do
  let dg = lookupDGraph ln libEnv
      emptyTh = case dgn_sign nodeLab of
        G_sign lid _ _ ->
            noSensGTheory lid (mkExtSign $ empty_signature lid) startSigId
      newN = getNewNodeDG dg
      newL = (newNodeLab emptyNodeName DGProof emptyTh)
             { globalTheory = Just emptyTh }
      morphism = propagateErrors "Utils.checkConservativityNode"
                 $ ginclusion logicGraph (dgn_sign newL) $
                   dgn_sign nodeLab
      lnk = (newN, nodeId, defDGLink
        morphism (ScopedLink Global DefLink $ getNodeConsStatus nodeLab)
        SeeSource)
      (tmpDG, _) = updateDGOnly dg $ InsertNode (newN, newL)
      (tempDG, InsertEdge lnk') = updateDGOnly tmpDG $ InsertEdge lnk
      tempLibEnv = Map.insert ln tempDG libEnv
  (str, _, (_, _, lnkLab), _) <-
    checkConservativityEdge useGUI lnk' tempLibEnv ln
  if isPrefixOf "No conservativity" str
    then return (str, libEnv, SizedList.empty)
    else do
         let nInfo = nodeInfo nodeLab
             nodeLab' = nodeLab { nodeInfo = nInfo { node_cons_status =
                          getEdgeConsStatus lnkLab } }
             changes = [ SetNodeLab nodeLab (nodeId, nodeLab') ]
             dg' = changesDGH dg changes
             history = snd $ splitHistory dg dg'
             libEnv' = Map.insert ln (groupHistory dg conservativityRule dg')
               libEnv
         return (str, libEnv', history)

getUsableConservativityCheckersForLogic :: Logic lid sublogics
    basic_spec sentence symb_items symb_map_items
    sign morphism symbol raw_symbol proof_tree
    => lid -> IO [ConservativityChecker sign sentence morphism]
getUsableConservativityCheckersForLogic lid = filterM (fmap isNothing . checkerUsable) $ conservativityCheck lid


getUsableConservativityCheckers :: LEdge DGLinkLab -> LibEnv -> LibName -> IO [G_conservativity_checker]
getUsableConservativityCheckers (_, target, _) libEnv ln = do
  Just (G_theory lidT _ _ _ _ _) <- return $ computeTheory libEnv ln target
  usableCCs <- getUsableConservativityCheckersForLogic lidT
  return $ G_conservativity_checker lidT <$> usableCCs


checkConservativityEdgeWith ::  LEdge DGLinkLab -> LibEnv -> LibName -> G_conservativity_checker
  -> IO (Result (Conservativity, G_theory, G_theory)) -- (conservativity, obligations holding in the source theory, obligations required to hold in an imported theory)
checkConservativityEdgeWith (source, target, linklab) libEnv ln (G_conservativity_checker lidCC cc) = do
  Just (G_theory lidT _ signT _ sensT _) <-
      return $ computeTheory libEnv ln target
  Just (G_theory lidS _ signS _ sensS _) <-
      return $ computeTheory libEnv ln source
  cc' <- coerceConservativityChecker lidCC lidT "checkconservativityOfEdge0" cc
  sensS' <- coerceThSens lidS lidT "checkconservativityOfEdge1" sensS
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
  let sensTransS = propagateErrors "checkConservativityEdge2"
        $ mapThSensValueM (map_sen lidT compMor) sensS'
  let sensTransS' = Set.fromList $ map sentence $ toNamedList sensTransS
      axiomsT = filter isAxiom $ toNamedList sensT
      inputSensT = filter ((`Set.notMember` sensTransS') . sentence) axiomsT
  case coerceSign lidS lidT "checkconservativityOfEdge.coerceSign" signS of
    Nothing -> fail "no implementation for heterogeneous links"
    Just signS' -> runResultT $ do
      (consv, outputSensT) <- ResultT $ checkConservativity cc'
                (plainSign signS', toNamedList sensS')
                compMor inputSensT
      let (explanations, obligations) = partition (`Set.member` sensTransS') outputSensT
      let theoryForObligations sens = G_theory {
            gTheoryLogic = lidT
            , gTheorySyntax = Nothing
            , gTheorySign = signT
            , gTheorySignIdx = startSigId
            , gTheorySens = toThSens $ fmap (\o -> (makeNamed "" o) {isAxiom = False}) sens
            , gTheorySelfIdx = startThId
          }
      return (consv, theoryForObligations explanations, theoryForObligations obligations)

conservativityResultToNewEdge :: LEdge DGLinkLab -> (Conservativity, G_theory, G_theory) -> (LEdge DGLinkLab, Bool)
conservativityResultToNewEdge (source, target, linklab) (consv, _, G_theory { gTheorySens = obligations }) =
  let consv' = if Map.null obligations then consv else Unknown "unchecked obligations"
      (newDglType, edgeChanged) = case dgl_type linklab of
        ScopedLink sc dl (ConsStatus consv'' cs op) ->
            let np = if consv' >= consv''
                      then Proven conservativityRule emptyProofBasis
                      else LeftOpen
            in (ScopedLink sc dl $
                  ConsStatus consv'' (max cs $ max consv'' consv') np, np /= op)
        t -> (t, False)
  in ((source, target, linklab { dgl_type = newDglType }), edgeChanged)

recordConservativityResult :: LEdge DGLinkLab -> LibEnv -> LibName -> (Conservativity, G_theory, G_theory) -> LibEnv
recordConservativityResult edge@(source, target, linklab) libEnv ln checkResult =
  let dg = lookupDGraph ln libEnv
      (provenEdge, edgeChanged) = conservativityResultToNewEdge edge checkResult
      edgeChanges = if edgeChanged then
                  [ DeleteEdge (source, target, linklab)
                  , InsertEdge provenEdge ] else []
      nextDG = changesDGH dg edgeChanges
  in if not edgeChanged then libEnv else
    Map.insert ln (groupHistory dg conservativityRule nextDG) libEnv


checkConservativityEdge :: Bool -> LEdge DGLinkLab -> LibEnv -> LibName
  -> IO (String, LibEnv, LEdge DGLinkLab, ProofHistory)
checkConservativityEdge useGUI link@(_, target, _) libEnv ln = do
  Just (G_theory lidT _ sigT _ _ _) <-
    return $ computeTheory libEnv ln target
  usableCs <- getUsableConservativityCheckersForLogic lidT
  checkerR <- conservativityChoser useGUI usableCs
  case maybeResult checkerR of
    Nothing -> return (concatMap diagString $ diags checkerR,
                        libEnv, link, SizedList.empty)
    Just theChecker -> do
      Result ds res <- checkConservativityEdgeWith link libEnv ln (G_conservativity_checker lidT theChecker)
      (_, showRes, newLibEnv, provenEdge) <- case res of
            Just conservativityResult@(consv, G_theory {gTheoryLogic = lidR1, gTheorySens = explanations}, G_theory {gTheoryLogic = lidR2, gTheorySens = obligations}) -> do
              explanations' <- toNamedList <$> coerceThSens lidR1 lidT "checkConservativityEdge" explanations
              obligations' <- toNamedList <$> coerceThSens lidR2 lidT "checkConservativityEdge" obligations
              let showObls = show . Pretty.vsep
                    . map (print_named lidT .
                                     mapNamed (simplify_sen lidT
                                        $ plainSign sigT))
              let libEnv' = recordConservativityResult link libEnv ln conservativityResult
              let (provenEdge', _) = conservativityResultToNewEdge link conservativityResult
              return (if null obligations' then consv
                else Unknown "unchecked obligations"
                , "The link is " ++ showConsistencyStatus consv
                ++ if null obligations' then
                    (if null explanations' then ""
                    else " because of the following axioms:\n"
                      ++ showObls explanations')
                  else " provided that the following obligations\n"
                     ++ "hold in an imported theory:\n"
                     ++ showObls obligations', libEnv', provenEdge')
            Nothing -> return (Unknown "Unknown", "Could not determine whether link is conservative", libEnv, link)
      let dg = lookupDGraph ln libEnv
          newDG = lookupDGraph ln newLibEnv
          history = snd $ splitHistory dg newDG
          myDiags = showRelDiags 4 ds
      return ( showRes ++ "\n" ++ myDiags
              , newLibEnv, provenEdge, history)

updateNodeProof :: LibName -> IntState -> LNode DGNodeLab
                -> G_theory -> (IntState, [DGChange])
updateNodeProof ln ost (k, dgnode) thry =
    case i_state ost of
      Nothing -> (ost, [])
      Just iist ->
        let le = i_libEnv iist
            dg = lookupDGraph ln le
            nn = getDGNodeName dgnode
            newDg = computeDGraphTheories le ln $ changeDGH dg
              $ SetNodeLab dgnode (k, dgnode { dgn_theory = thry })
            history = reverse $ flatHistory $ snd $ splitHistory dg newDg
            nst = add2history
                    (CommentCmd $ "basic inference done on " ++ nn ++ "\n")
                    ost [DgCommandChange ln]
            nwst = nst { i_state =
                           Just iist { i_libEnv = Map.insert ln newDg le } }
        in (nwst, history)
