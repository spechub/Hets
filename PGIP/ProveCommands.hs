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

module PGIP.ProveCommands
       ( shellTranslate
       , shellProver
       , shellProve
       ) where

import System.Console.Shell.ShellMonad

import PGIP.CMDLState
import PGIP.CMDLUtils
import PGIP.CMDLShell

import Static.DevGraph
import Static.DGToSpec

import Common.Result
import Common.DocUtils
import Common.Doc
import Common.ResultT
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
import Proofs.AbstractState

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

translateProofStatus :: (Logic lid1 sublogics1 basic_spec1
                        sentence1 symb_items1 symb_map_items1
                        sign1 morphism1 symbol1 raw_symbol1
                        proof_tree1
--                        ,Logic lid sublogics basic_spec
--                        sentence symb_items symb_map_items
--                        sign morphism symbol raw_symbol
--                        proof_tree
                        ) =>
                        ProofState lid1 sentence1 ->
                        AnyComorphism ->
                        Maybe (ProofState lid1 sentence1)
translateProofStatus ps cm'
 = Just ps 
{- 
 case mapG_theory cm' $ theory ps of
    Result _ (Just nth) ->
--       do
       let thN = theoryName ps
           pm = proversMap ps
           cm = comorphismsToProvers ps
           lid'=logicId ps
--       ps'<- initialState lid' thN nth pm cm
       in 
         Just $ ps {
                  theory = nth,
                  sublogicOfTheory = sublogicOfTh nth,
                  lastSublogic = sublogicOfTh nth,
                  selectedTheory = nth
                  }
    _ -> Nothing
-}
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
          
          ne=map (\x-> case x of 
                        Element ps nb ->
                         case translateProofStatus ps cm of
                           Just ps' ->
                              (Element ps' nb, "")
                           _->(x,genMsg $ nb )) 
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
            foldl (\ l p -> 
                         if P.hasProverKind 
                            P.ProveCMDLautomatic p
                         then (G_prover (targetLogic cid) 
                               p,cm):l
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
             (Element z _):_->case find (\(y,_)->
                                     (getPName' y)==inp) $
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
      -- composition of comorphism !! instead of applyint to the list
      x -> case find (\(y,_)-> (getPName' y)==inp)
                   $ getProversCMDLautomatic x of
            Nothing -> return state {
                            errorMsg="Wrong prover name"
                            }
            Just (p,_) -> return state {
                                  proveState = Just pS {
                                              prover = Just p
                                         }
                              }


proveNode :: (Logic lid sublogics1
              basic_spec1
              sentence
              symb_items1
              symb_map_items1
              sign1
              mophism1
              symbol1
              raw_symbol1
              poof_tree1) =>
              ProofState lid sentence ->
              (G_prover,AnyComorphism)
               -> IO ()
proveNode st p_cm@(_,acm) 
 = do
     axmLs <- axiomMap st 
     let st' = st {
                 selectedGoals = Map.keys $ selectedGoalMap st
                ,includedAxioms = Map.keys axmLs
                }
     s <- recalculateSublogicAndSelectedTheory st'
     putStrLn $ "Sel Goals: " ++ (show $ selectedGoals s)
     putStrLn $ "Incl Axioms: " ++ (show $ includedAxioms s)
     p_cm1 <- lookupKnownProver s P.ProveCMDLautomatic
     case prepareForProving s p_cm1 of
       Result _ Nothing -> do
                            putStrLn "Could not prepare prove"
                            return ()
       Result _ (Just (G_theory_with_prover lid th@(P.Theory sign sens) p)) ->
        case P.proveCMDLautomatic p of
--         case P.proveGUI p of
         Nothing -> do
                     putStrLn "Could not find prover !!"
                     return ()
         Just fn ->
          do
           putStrLn $ showDoc sign "\n" ++ 
                      show (vsep $ map (print_named lid) (P.toNamedList sens))
           -- print the list of axioms
           putStrLn $ show $ selectedGoalMap s
           a <- axiomMap s
           putStrLn $ show a
           --putStrLn $ show $ axiomMap s
           tmp <- fn (theoryName st) (P.Tactic_script "")  th
--           tmp <- fn (theoryName st) th
           putStrLn $ show tmp
--           case tmp of
--            Result _ Nothing -> do
--                                 putStrLn "Could not prove"
--                                 return ()
--            Result _ (Just s) -> putStrLn $ show s

--      ps <- lift $ (proveCMDLautomaic p) (theoryName st) th
--      let tmp =  markProved acm lid ps st
--          (_,oldContents) = labNode' (safeContextDG
--                              "PGIP.ProveCommands.proveNode"
--                              dGraph node)


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
          case uComorphisms pS of
           [] -> return 
                     state{errorMsg="No comorphism selected"}
           cm:_ ->
             case elements pS of
              [] -> return state{errorMsg="Nothing selected"}
              (Element sm _):_ ->
                    do 
                     proveNode sm (prv,cm)
                     return state
--        (nwel, nwst) <- proveNodes (elements pS) prv dgS []
--          return state {
--                  devGraphState = Just nwst,
--                  proveState = Just pS {
--                                elements = nwel
--                                }
--                 }

shellProve :: Sh CMDLState ()
shellProve
 = shellComWithout cProve

-- !?
-- it does not really make sense to have a prove all
-- command once we have a select all command 
-- cProveAll::CMDLState -> CMDLState
-- 
