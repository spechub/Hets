{-# OPTIONS -cpp #-}
{- |
Module      :$Header$
Description : CMDL interface commands
Copyright   : uni-bremen and DFKI
Licence     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@iu-bremen.de
Stability   : provisional
Portability : portable

PGIP.ProveCommands contains all commands 
related to prove mode 
-} 

module PGIP.ProveCommands where

import System.Console.Shell.ShellMonad

import PGIP.CMDLState
import PGIP.CMDLUtils
import PGIP.CMDLShell

import Static.DevGraph
import Static.DGToSpec

import Common.Result
import Common.AS_Annotation
import Common.Utils
import qualified Common.OrderedMap as OMap


import Data.List
import Data.Graph.Inductive.Graph
import qualified Data.Map as Map
import qualified Data.Set as Set 

import Comorphisms.LogicGraph

import Proofs.EdgeUtils
import Proofs.StatusUtils

import Logic.Grothendieck
import Logic.Comorphism
import Logic.Coerce
import Logic.Logic
import qualified Logic.Prover as P

import Syntax.AS_Library

-- apply comorphisms
shellTranslate :: String -> Sh CMDLState ()
shellTranslate
 = shellComWith cTranslate

-- select a prover
shellProver :: String -> Sh CMDLState ()
shellProver
 = shellComWith cProver


-- | apply comorphisms 
cTranslate::String -> CMDLState -> IO CMDLState
cTranslate input state =
 case proveState state of
  -- nothing selected !
  Nothing ->return state {
                    errorMsg="Nothing selected"
                    }
  Just pS ->
   -- parse the comorphism name
   case lookupComorphism_in_LG $ trim input of
    Result _ (Just cm) -> 
     do
      -- translate all selected theories if possible
      let genMsg nb = 
            case devGraphState state of
             Nothing -> "Error finding loaded library"
             Just dgS->
              case find (\(n,_)-> n==nb) $ getAllNodes dgS of
               Nothing -> "Could not find node number"
               Just (_,lb) -> "Node "++(getDGNodeName lb)++
                              " could not be translated"
          ne=map (\x-> case mapG_theory cm $ theory x of
                        Result _ (Just nth)->(x{theory = nth},
                                              "")
                        _->(x,genMsg $ nodeNumber x )) 
                                          $ elements pS
          msg' = concatMap (\(_,m) -> case m of 
                                       [] -> []
                                       _ -> [m] ) ne
          ne' = map (\(t,_) -> t) ne 
          -- add the comorphism to the comorphisms list     
          ncl = [cm] ++ (uComorphisms pS)     
      prettyPrintList msg'    
      return state {
               proveState = Just pS {
                                 elements = ne',
                                 uComorphisms = ncl
                                 }
                   }
    _ -> return state {
                 errorMsg = "Wrong parameters"
                 }



getProversCMDLautomatic::[AnyComorphism]->[(G_prover,AnyComorphism)]
getProversCMDLautomatic = foldl addProvers []
     where addProvers acc cm =
             case cm of
             Comorphism cid -> acc ++
                 foldl (\ l p -> if P.hasProverKind P.ProveCMDLautomatic p
                                    then (G_prover (targetLogic cid) p,cm):l
                                    else l)
                       []
                       (provers $ targetLogic cid)


-- | select a prover
cProver::String -> CMDLState -> IO CMDLState
cProver input state =
  do
   -- trimed input
   let inp = trim input
       getPName' x = case x of
                      (G_prover _ p)-> P.prover_name p
   case proveState state of
    Nothing -> return state {
                        errorMsg = "Nothing selected"
                        }
    Just pS ->
     -- see if any comorphism was used
     case uComorphisms pS of
       -- if none use the identity comorphism of the theory
       -- of the first selected node
      [] -> case elements pS of
             [] -> return state {
                           errorMsg ="Nothing selected"
                           }
             z:_->case find (\(y,_)->(getPName' y)==inp) $
                        getProversCMDLautomatic $
                        findComorphismPaths logicGraph $
                        sublogicOfTh $ theory z of
                   Nothing -> return state {
                                 errorMsg="Wrong prover name"
                                 }
                   Just (p,_)->return state {
                                proveState=Just pS {
                                             prover = Just p
                                            }
                              }
      -- if yes,  use the comorphism to find a list 
      -- of provers
      x -> case find (\(y,_)-> (getPName' y)==inp
                        ) $ getProversCMDLautomatic x of
              Nothing -> return state {
                            errorMsg="Wrong prover name"
                            }
              Just (p,_) -> return state {
                              proveState = Just pS {
                                             prover = Just p
                                         }
                              }

-- mark all newly proven goals with their proof tree
-- this function is a copy of the one defined in 
-- Proof.InferBasic and is done because InferBasic can
-- not compile without UNI_PACKAGE
markProved :: (Ord a, Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree) =>
       AnyComorphism -> lid -> [P.Proof_status proof_tree]
    -> P.ThSens a (AnyComorphism,BasicProof)
    -> P.ThSens a (AnyComorphism,BasicProof)
markProved c lid status thSens = foldl upd thSens status
    where upd m pStat = OMap.update (updStat pStat) 
                                   (P.goalName pStat) m
          updStat ps s = Just $
                s { senAttr = P.ThmStatus $ 
                         (c,BasicProof lid ps):P.thmStatus s}


-- | The function 'proveNodes' provides basic proving of 
-- a node list
proveNodes :: [CMDLProveElement] ->G_prover -> 
              CMDLDevGraphState-> [CMDLProveElement]
           -> IO ([CMDLProveElement],CMDLDevGraphState)
proveNodes ls prv state addTo = case ls of
    x:l -> do
      let dGraph = lookupDGraph (ln state) (libEnv state)
          thForProof = theory x
      case thForProof of
        G_theory lid1 sig ind thSens _ -> do
          let nodeName = case find (\(n,_)-> n== nodeNumber x)
                                $ getAllNodes state of
                          Nothing -> "Unkown node"
                          Just (_,ll)-> getDGNodeName ll
              thName = shows (getLIB_ID $ ln state) "_" 
                          ++ nodeName
            --  Proving
          case prv of
            G_prover plid p -> do
             -- coerce to prover lid
              let (aMap,gMap) = Map.partition(isAxiom . 
                                         OMap.ele) thSens
              ths <- coerceThSens lid1 lid1
                      ("PGIP.ProveCommands.proveNodes" ++
                       " : selected goals") gMap
              let (sel_goals, other_goals) =
                              let selected k _ = not $ 
                                       Set.member k Set.empty
                              in Map.partitionWithKey 
                                              selected ths
                  provenThs=Map.filter(\y->isProvenSenStatus $
                                           OMap.ele y) 
                                               sel_goals
                                               --  other_goals
                  sel_provenThs = OMap.map(\y->y{
                                             isAxiom=True}) $
                                 filterMapWithList(OMap.keys 
                                              gMap) provenThs
                  sel_sens = filterMapWithList (OMap.keys 
                                              aMap) thSens
              bTh' <- coerceBasicTheory lid1 lid1
                          ("PGIP.ProveCommands.proveNodes"++
                           ": basic theory")
                                (sig, P.toNamedList $
                                Map.union sel_sens $
                                Map.union sel_provenThs 
                                          sel_goals)
              let (sign'',sens'') = bTh'
              p' <- coerceProver plid lid1 "" p
              putStrLn "---------gMap------------------------ "
              putStrLn $ show gMap
              putStrLn "---------lid1-------------------------"
              putStrLn $ show lid1
              putStrLn "----------other_goals-----------------"
              putStrLn $ show other_goals
              putStrLn "----------sel_goals-------------------"
              putStrLn $ show sel_goals
              putStrLn "----------bTh'------------------------"
              putStrLn $ show bTh'
              putStrLn "-----------sel_sens-------------------"
              putStrLn $ show sel_sens
              putStrLn "-----------sel_provenThs--------------"
              putStrLn $ show sel_provenThs
              putStrLn "------------provenThs------------------"
              putStrLn $ show provenThs
              putStrLn "------------sign''---------------------"
              putStrLn $ show sign''
              putStrLn "-------------sens''---------------------"
              putStrLn $ show sens''
             -- apply function ?!
              case (P.proveCMDLautomatic p') of
                Nothing ->  do
                            putStrLn "Could not find prover command"
                            proveNodes l prv state addTo
                Just fn -> do
                  putStrLn "prove command found"
                  ps <- fn thName (P.Tactic_script "")
                                      $ P.Theory sign''
                                      $ P.toThSens sens''
                  case ps of
                    Result _ Nothing -> do
                           putStrLn "Could not prove"
                           proveNodes l prv state addTo
                    Result _ (Just pps) -> do
                     putStrLn $ show pps
                     let provedOrDisproved 
                          allSentencesIncluded senStat =
                              P.isProvedStat senStat || 
                              allSentencesIncluded
                              && case P.goalStatus senStat of
                                        P.Disproved -> True
                                        _ -> False
                         nwgoalMap = (markProved $ Comorphism
                                      $ mkIdComorphism lid1 $ 
                                      top_sublogic lid1)
                                      lid1
                                      (filter
                                      (provedOrDisproved $ 
                                      null $ OMap.keys thSens)
                                      pps) gMap
                         newTh = G_theory lid1 sig ind
                                  (Map.union thSens 
                                    nwgoalMap) 0
                         (_,oldContents) =
                              labNode' (safeContextDG
                              "PGIP.Common.proveNodes"
                               dGraph $ nodeNumber x)
                         newNodeLab = oldContents{
                                         dgn_theory = newTh}
                         (nextDGraph,changes) =
                              updateWithOneChange 
                              (SetNodeLab (error "proveNodes")
                              (nodeNumber x,newNodeLab)
                              ) dGraph []
                         rules = []
                         nextHistoryElem = (rules, changes)
                         result = mkResultProofStatus 
                                    (ln state) 
                                    (libEnv state)
                                    nextDGraph nextHistoryElem
                     proveNodes l prv (state {
                                           libEnv=result
                                           })
                                ((x { theory = newTh }):addTo)
    [] -> return (addTo,state)
   

cProve::CMDLState ->IO CMDLState
cProve state
 = case proveState state of
    Nothing -> return state {errorMsg = "Nothing selected" }
    Just pS ->
     case prover pS of
      Nothing -> return state {errorMsg="No prover selected"}
      Just prv->
       case devGraphState state of
        Nothing -> return state{errorMsg="No library loaded"}
        Just dgS ->
         do
          (nwel, nwst) <- proveNodes (elements pS) prv dgS []
          return state {
                  devGraphState = Just nwst,
                  proveState = Just pS {
                                elements = nwel
                                }
                 }

shellProve :: Sh CMDLState ()
shellProve
 = shellComWithout cProve

-- !?
-- it does not really make sense to have a prove all
-- command once we have a select all command 
-- cProveAll::CMDLState -> CMDLState
