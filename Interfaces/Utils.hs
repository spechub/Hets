{-# OPTIONS -cpp #-}
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
         , addProveToHist
         , proofTreeToProve
         , wasProved
         , convertGoal
         , parseTimeLimit
         , mergeGoals
         , emptyCommandHistory
         , addCommandHistoryToState
         , checkConservativityEdge
         ) where


import Interfaces.DataTypes
import Interfaces.GenericATPState

import Data.Graph.Inductive.Graph
import Data.Maybe (fromMaybe)
import Data.List (isPrefixOf, stripPrefix, nubBy)
import Data.IORef
import Data.Map (insert)

import Static.DevGraph
import Static.GTheory

import Proofs.AbstractState
import Proofs.TheoremHideShift
import Proofs.EdgeUtils

import Driver.Options (rmSuffix)

import System.Directory (getCurrentDirectory)

import Logic.Comorphism
import Logic.Prover
import Logic.Logic
import Logic.Grothendieck
import Logic.Coerce

import qualified Common.OrderedMap as OMap
import Common.Utils (joinWith, splitOn)
import Common.Result
import Common.LibName
import Common.Id (nullRange)
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
getAllEdges st
 = labEdgesDG $ lookupDGraph (i_ln st) (i_libEnv st)


-- | Constructor for CMDLProofGUIState datatype
initNodeInfo:: (Logic lid1 sublogics1
         basic_spec1 sentence1 symb_items1 symb_map_items1
         sign1 morphism1 symbol1 raw_symbol1 proof_tree1) =>
         ProofState lid1 sentence1 -> Int
         -> Int_NodeInfo
initNodeInfo = Element

emptyIntIState :: LibEnv -> LIB_NAME -> IntIState
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
    script = ATPTactic_script {
                 ts_timeLimit = 20,
                 ts_extraOpts = [] },
    loadScript = False
    }

emptyIntState :: IntState
emptyIntState =
    IntState { i_state = Just $ emptyIntIState emptyLibEnv $ Lib_id $
                                               Indirect_link "" nullRange
                                                             "" noTime
             , i_hist  = IntHistory { undoList = []
                                    , redoList = [] }
             , filename = []
             }

-- Create an empty command history
emptyCommandHistory :: IORef IntState -> IO (Result CommandHistory)
emptyCommandHistory st = do
  ch <- newIORef []
  ost <- readIORef st
  ff <- tryRemoveAbsolutePathComponent $ filename ost
  return $ Result [] $ Just CommandHistory { hist = ch,
                                             filePath = rmSuffix ff}

-- If an absolute path is given,
-- it tries to remove the current working directory as prefix of it.
tryRemoveAbsolutePathComponent :: String -> IO String
tryRemoveAbsolutePathComponent f
   | "/" `isPrefixOf` f = do
                           dir <- getCurrentDirectory
                           return $ fromMaybe f (stripPrefix (dir ++ "/") f)
   | otherwise        = return f

-- If at least one goal was proved and the prove is not the same as last time
-- the prove gets added, otherwise not.
addProveToHist :: CommandHistory
        -> ProofState lid sentence         -- current proofstate
        -> Maybe (G_prover, AnyComorphism) -- possible used translation
        -> [Proof_status proof_tree]       -- goals included in prove
        -> IO ()
addProveToHist ch st pcm pt
    | Prelude.null $ Prelude.filter wasProved pt = return ()
    | otherwise = do
                  p <- proofTreeToProve ch st pcm pt
                  addToHist ch p

-- Converts a list of proof-trees to a prove
proofTreeToProve :: CommandHistory
     -> ProofState lid sentence  -- current proofstate
     -> Maybe (G_prover, AnyComorphism) -- possible used translation
     -> [Proof_status proof_tree] -- goals included in prove
     -> IO ProveCommand
proofTreeToProve ch st pcm pt =
  do
  -- selected prover
  let prvr = maybe (selectedProver st) (Just . getProverName .fst ) pcm
  -- selected translation
      trans = maybe Nothing (Just . snd) pcm
  -- 1. filter out the not proven goals
  -- 2. reverse the list, because the last proven goals are on top
  -- 3. convert all proof-trees to goals
  -- 4. merge goals with same used axioms
      goals = mergeGoals $ Prelude.reverse $ Prelude.map convertGoal
              $ Prelude.filter wasProved pt
  -- axioms to include in prove
      allax = case theory st of
                 G_theory _ _ _ axs _ -> OMap.keys axs
      nodeName = dropName (filePath ch) $ theoryName st
  return Prove { nodeNameStr = nodeName,
                 usedProver = prvr,
                 translation = trans,
                 provenGoals = goals,
                 allAxioms = allax}

dropName :: String -> String -> String
dropName fch s = maybe s Prelude.tail (stripPrefix fch s)

-- This checks wether a goal was proved or not
wasProved :: Proof_status proof_Tree -> Bool
wasProved g = case goalStatus g of
    Proved _  -> True
    _         -> False

-- Converts a proof-tree into a goal.
convertGoal :: Proof_status proof_tree -> ProvenGoal
convertGoal pt =
  ProvenGoal {name = goalName pt, axioms = usedAxioms pt, time_Limit = tLimit}
  where
     (Tactic_script scrpt) = tacticScript pt
     tLimit = maybe 20 read (parseTimeLimit $ splitOn '\n' scrpt)

-- Parses time-limit from the tactic-script of a goal.
parseTimeLimit :: [String] -> Maybe String
parseTimeLimit l =
    if Prelude.null l' then Nothing else Just
                               $ Prelude.drop (length tlStr) $ last l'
    where
       l' = Prelude.filter (isPrefixOf tlStr) l
       tlStr = "Time limit: "

-- Merges goals with the same used axioms into one goal.
mergeGoals :: [ProvenGoal] -> [ProvenGoal]
mergeGoals []     = []
mergeGoals (h:[]) = [h]
mergeGoals (h:t) | mergeAble h h' = mergeGoals $ merge h h':Prelude.tail t
                 | otherwise      = h:mergeGoals t
                 where
                    h' = Prelude.head t
                    mergeAble :: ProvenGoal -> ProvenGoal -> Bool
                    mergeAble a b = axioms a == axioms b &&
                                    time_Limit a == time_Limit b
                    merge :: ProvenGoal -> ProvenGoal -> ProvenGoal
                    merge a b = a{name = name a ++ ' ':name b}



addCommandHistoryToState :: CommandHistory -> IORef IntState -> IO (Result ())
addCommandHistoryToState ch ioSt
 = do
    ost <- readIORef ioSt
    lsch <- readIORef $ hist ch
    let z = Int_CmdHistoryDescription {
             cmdName = joinWith '\n' $ Prelude.map show lsch,
             cmdDescription = [ IStateChange $ i_state ost ]
             }
        nwst = ost { i_hist = (i_hist ost) {
                                undoList = z: (undoList $ i_hist ost)}}
    writeIORef ioSt nwst
    return $ Result [] $ Just ()


conservativityRule :: DGRule
conservativityRule = DGRule "ConservativityCheck"

conservativityChoser :: Bool ->[ConservativityChecker sign sentence morphism]
                       -> IO
                           (Result (ConservativityChecker
                            sign sentence morphism))
conservativityChoser useGUI checkers = case checkers of
  [] -> return $ fail "No conservativity checker available"
  hd : tl ->
#ifdef UNI_PACKAGE
    if useGUI && not (null tl) then do
      chosenOne <- listBox "Pic a conservativity checker"
                                $ Prelude.map checker_id checkers
      case chosenOne of
        Nothing -> return $ fail "No conservativity checker chosen"
        Just i -> return $ return $ checkers !! i
   else
#endif
   return $ return hd

consToCons :: ConsistencyStatus -> Conservativity
consToCons Conservative = Cons
consToCons Monomorphic  = Mono
consToCons Definitional = Def
consToCons _            = None

checkConservativityEdge :: Bool -> (LEdge DGLinkLab) -> LibEnv -> LIB_NAME
                           -> IO (String,LibEnv, ProofHistory)
checkConservativityEdge useGUI (source,target,linklab) libEnv ln
 = do
    let thTar =
         case computeTheory libEnv ln target of
          Result _ (Just th1) -> th1
          _ -> error "checkconservativityOfEdge: computeTheory"
    G_theory lid _sign _ sensTar _ <- return thTar
    GMorphism cid _ _ morphism2 _ <- return $ dgl_morphism linklab
    morphism2' <- coerceMorphism (targetLogic cid) lid
                 "checkconservativityOfEdge" morphism2
    let compMor = case dgn_sigma $ labDG (lookupDGraph ln libEnv) target of
          Nothing -> morphism2'
          Just (GMorphism cid' _ _ morphism3 _) -> case
            do morphism3' <- coerceMorphism (targetLogic cid') lid
                   "checkconservativityOfEdge" morphism3
               comp morphism2' morphism3' of
                 Result _ (Just phi) -> phi
                 _ -> error "checkconservativityOfEdge: comp"
    let thSrc =
         case computeTheory libEnv ln source of
           Result _ (Just th1) -> th1
           _ -> error "checkconservativityOfEdge: computeTheory"
    G_theory lid1 sign1 _ sensSrc1 _ <- return thSrc
    sign2 <- coerceSign lid1 lid "checkconservativityOfEdge.coerceSign" sign1
    sensSrc2 <- coerceThSens lid1 lid "checkconservativityOfEdge1" sensSrc1
    let transSensSrc = propagateErrors
         $ mapThSensValueM (map_sen lid compMor) sensSrc2
    if length (conservativityCheck lid) < 1
        then return ( "No conservativity checkers available"
                    , libEnv
                    , SizedList.empty)
        else
         do
          checkerR <- conservativityChoser useGUI $ conservativityCheck lid
          if hasErrors $ diags checkerR
           then return ( "No conservativity checker chosen"
                       , libEnv
                       , SizedList.empty)
           else
            do
             let chCons = checkConservativity $
                          fromMaybe (error "checkconservativityOfEdge")
                             $ maybeResult checkerR
                 inputThSens = nubBy (\ a b -> sentence a == sentence b) $
                               toNamedList $
                               sensTar `OMap.difference` transSensSrc
                 Result ds res =
                     chCons
                        (plainSign sign2, toNamedList sensSrc2)
                        compMor inputThSens
                 consShow = case res of
                            Just (Just (cst, _)) -> cst
                            _                    -> Unknown "Unknown"
                 cs' = consToCons consShow
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
                 newSens = [ makeNamed "" o | o<-obligations ]
                 namedNewSens = toThSens [ o { isAxiom = False } |
                                           o<-inputThSens, n<-newSens,
                                           sentence o == sentence n ]
             G_theory glid gsign gsigid gsens gid <- return $ dgn_theory nodelab
             namedNewSens' <- coerceThSens lid glid "" namedNewSens
             let oldSens = OMap.toList gsens
                 -- Sort out the named sentences which have a different name,
                 -- but same sentence
                 mergedSens = nubBy (\(_,a) (_,b) -> sentence a == sentence b) $
                              oldSens ++ OMap.toList namedNewSens'
                 (newTheory, nodeChange) =
                   (G_theory glid gsign gsigid (OMap.fromList mergedSens) gid,
                    length oldSens /= length mergedSens)
                 newTargetNode = (target
                                 ,nodelab { dgn_theory = newTheory })
                 nodeChanges = [ SetNodeLab nodelab newTargetNode | nodeChange ]
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
                               ++ (show $ Pretty.vsep $ map (print_named glid .
                                   mapNamed (simplify_sen glid sig1)) lst)
                 showRes = case res of
                           Just (Just (cst,_)) -> "The link is "
                            ++ showConsistencyStatus cst
                            ++ (showObls $ toNamedList namedNewSens')
                           _ -> "Could not determine whether link is "
                                 ++ "conservative"
                 myDiags = showRelDiags 2 ds
             return ( showRes ++ "\n" ++ myDiags
                    , newLibEnv
                    , history)


