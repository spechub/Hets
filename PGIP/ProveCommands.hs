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
       , shellProveAll
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


import Control.Concurrent as Concurrent 

-- apply comorphisms
shellTranslate :: String -> Sh CMDLState ()
shellTranslate
 = shellComWith cTranslate

-- select a prover
shellProver :: String -> Sh CMDLState ()
shellProver
 = shellComWith cProver



-- | select comorphisms 
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
    Result _ Nothing -> return state {
                                errorMsg = "Wrong comorphism name"
                                }
    Result _ (Just cm) -> 
     do
      case cComorphism pS of 
       -- no comorphism used before
       Nothing -> 
        return state {
                proveState = Just pS {
                                  cComorphism = Just cm
                                  }
                        }
       Just ocm -> 
        return state {
                proveState = Just pS {
                                  cComorphism = compComorphism ocm cm
                                  }
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
   case proveState state of
    Nothing -> return state {
                        errorMsg = "Nothing selected"
                        }
    Just pS ->
     -- check that some theories are selected
     case elements pS of
      [] -> return state {
                errorMsg="Nothing selected"
                }
      (Element z _):_ ->
        -- see if any comorphism was used
       case cComorphism pS of
       -- if none use the theory  of the first selected node
       -- to find possible comorphisms
       Nothing-> case find (\(y,_)->
                                (getPName y)==inp) $
                        getProversCMDLautomatic $
                        findComorphismPaths logicGraph $
                        sublogicOfTh $ theory z of
                   Nothing -> return state {
                                 errorMsg="No applicable prover with"
                                          ++" this name found"
                                 }
                   Just (p,_)->return state {
                                proveState=Just pS {prover = Just p }
                                            }
       -- if yes,  use the comorphism to find a list 
       -- of provers
       Just x -> 
         case find (\(y,_)-> (getPName y)==inp)
                   $ getProversCMDLautomatic [x] of
            Nothing -> 
             case find (\(y,_) ->
                             (getPName y)==inp) $
                      getProversCMDLautomatic $
                      findComorphismPaths logicGraph $
                      sublogicOfTh $ theory z of
               Nothing -> return state {
                             errorMsg="No applicable prover with"
                                      ++" this name found"
                                      }
               Just (p,nCm@(Comorphism cid))-> return state {
                               errorMsg="Prover can be used with the " 
                                ++"comorphism selected using translate"
                                ++" command. Using comorphism : "
                                ++ language_name cid
                             , proveState = Just pS {
                                             cComorphism=Just nCm
                                             ,prover = Just p
                                             }
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
              --use theorems is subsequent proofs
              Bool ->
              -- save problem file for each goal
              Bool ->
              -- Tactic script
              String ->
              -- proofState of the node that needs proving
              -- all theorems, goals and axioms should have 
              -- been selected before,but the theory should have
              -- not beed recomputed
              ProofState lid sentence ->
              -- selected prover, if non one will be automatically 
              -- selected
              Maybe G_prover ->
              -- selected comorphism, if non one will be automatically
              -- selected
              Maybe AnyComorphism ->
              -- the first String represents the error messages
               IO (String)
proveNode useTh save2File scriptTxt pf_st mp mcm  
 = do
    -- recompute the theory (to make effective the selected axioms,
    -- goals)
    st <- recalculateSublogicAndSelectedTheory pf_st
    -- compute a prover,comorphism pair to be used in preparing 
    -- the theory
    p_cm<-case mcm of 
           Nothing -> lookupKnownProver st P.ProveCMDLautomatic
           Just cm' ->
            case mp of
             Nothing-> lookupKnownProver st P.ProveCMDLautomatic
             Just p' -> return (p',cm')
   -- try to prepare the theory          
    prep <- case prepareForProving st p_cm of
             Result _ Nothing -> 
               do
                p_cm' <- lookupKnownProver st P.ProveCMDLautomatic
                return $ case prepareForProving st p_cm' of
                          Result _ Nothing -> Nothing
                          Result _ (Just sm)-> Just sm
             Result _ (Just sm) -> return $ Just sm
    case prep of
     -- theory could not be computed 
     Nothing -> return ("No suitable prover and comorphism found")
     Just (G_theory_with_prover lid th p) ->  
      case P.proveCMDLautomaticBatch p of
         Nothing -> return ("Error obtaining the prover")
         Just fn ->
          do
          answ <- Concurrent.newEmptyMVar
          tmp <- fn useTh -- use theorems is subsequent proves
                    save2File -- safe file for each prove!?
                    answ
                    (theoryName st)
                    (P.Tactic_script scriptTxt)
                    th
          answ' <- takeMVar answ        
          putStrLn $ show $ answ'          
          return ""

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


cProveAll::CMDLState ->IO CMDLState
cProveAll state
 = case proveState state of
    Nothing -> return state {errorMsg = "Nothing selected" }
    Just pS ->
     case devGraphState state of
      Nothing -> return state{errorMsg="No library loaded"}
      Just dgS ->
       do
        case elements pS of
         [] -> return state{errorMsg="Nothing selected"}
         (Element sm _):_ ->
           do 
            proveNode (useTheorems pS) (save2file pS)
                      (script pS) sm (prover pS) (cComorphism pS)
            return state
--        (nwel, nwst) <- proveNodes (elements pS) prv dgS []
--          return state {
--                  devGraphState = Just nwst,
--                  proveState = Just pS {
--                                elements = nwel
--                                }
--                 }

shellProveAll :: Sh CMDLState ()
shellProveAll
 = shellComWithout cProveAll

-- !?
-- it does not really make sense to have a prove all
-- command once we have a select all command 
-- cProveAll::CMDLState -> CMDLState
--
--
--
--
--
--
--
--
--
--
--
--
----     axmLs <- axiomMap st 
--     let st' = st {
--                 selectedGoals = Map.keys $ selectedGoalMap st
--                ,includedAxioms = Map.keys axmLs
--                }
 
