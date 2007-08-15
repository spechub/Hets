{-# OPTIONS -cpp #-}
{- |
Module      :$Header$
Description : CMDL interface commands
Copyright   : uni-bremen and DFKI
Licence     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@iu-bremen.de
Stability   : provisional
Portability : portable

PGIP.InfoCommands contains all commands 
that provides information about the state
of the development graph and selected
theories
-} 

module PGIP.InfoCommands
       ( shellShowDgGoals
       , shellShowTheoryGoals
       , shellShowTheoryCurrent
       , shellShowTheory
       , shellInfoCurrent
       , shellInfo
       , shellShowTaxonomyCurrent
       , shellShowTaxonomy
       , shellShowConceptCurrent
       , shellShowConcept
       , shellNodeNumber
       , shellEdges
       , shellNodes
       , shellDisplayGraph
       , shellShowTheoryGoalsCurrent
       , shellShowNodePGoals
       , shellShowNodePGoalsCurrent
       , shellShowNodeUGoals
       , shellShowNodeUGoalsCurrent
       , shellShowNodeAxioms
       , shellShowNodeAxiomsCurrent
       ) where

import System.Console.Shell.ShellMonad

#ifdef UNI_PACKAGE
import Events
import Destructible
import GUI.Taxonomy
import GUI.ShowGraph
#endif

import PGIP.CMDLState
import PGIP.CMDLUtils
import PGIP.CMDLShell

import Static.GTheory
import Static.DevGraph

import Common.DocUtils
import Common.AS_Annotation
import Common.Taxonomy
import qualified Common.OrderedMap as OMap

import Data.Graph.Inductive.Graph
import qualified Data.Set as Set
import Data.List
import qualified Data.Map as Map

import Logic.Grothendieck
import Logic.Logic

import Driver.Options


shellShowNodePGoals :: String -> Sh CMDLState ()
shellShowNodePGoals 
 = shellComWith cShowNodePGoals False False

shellShowNodePGoalsCurrent :: Sh CMDLState ()
shellShowNodePGoalsCurrent 
 = shellComWithout cShowNodePGoalsCurrent False False

shellShowNodeUGoals :: String -> Sh CMDLState ()
shellShowNodeUGoals 
 = shellComWith cShowNodeUGoals False False

shellShowNodeUGoalsCurrent :: Sh CMDLState ()
shellShowNodeUGoalsCurrent
 = shellComWithout cShowNodeUGoalsCurrent False False

shellShowNodeAxioms :: String -> Sh CMDLState ()
shellShowNodeAxioms
 = shellComWith cShowNodeAxioms False False

shellShowNodeAxiomsCurrent :: Sh CMDLState ()
shellShowNodeAxiomsCurrent
 = shellComWithout cShowNodeAxiomsCurrent False False


-- show list of all goals
shellShowDgGoals :: Sh CMDLState ()
shellShowDgGoals
 = shellComWithout cShowDgGoals False False
shellShowTheoryGoalsCurrent :: Sh CMDLState ()
shellShowTheoryGoalsCurrent
 = shellComWithout cShowTheoryGoalsCurrent False False
-- show theory of all goals
shellShowTheoryGoals :: String -> Sh CMDLState ()
shellShowTheoryGoals
 = shellComWith cShowTheoryGoals False False
-- show theory of selection
shellShowTheoryCurrent :: Sh CMDLState ()
shellShowTheoryCurrent
 = shellComWithout cShowTheoryCurrent False False
-- show theory of input nodes
shellShowTheory :: String -> Sh CMDLState ()
shellShowTheory
 = shellComWith cShowTheory False False
-- show all information of selection
shellInfoCurrent :: Sh CMDLState ()
shellInfoCurrent
 = shellComWithout cInfoCurrent False False
-- show all information of input
shellInfo :: String -> Sh CMDLState ()
shellInfo 
 = shellComWith cInfo False False 
-- show taxonomy of selection
shellShowTaxonomyCurrent :: Sh CMDLState ()
shellShowTaxonomyCurrent
 = shellComWithout cShowTaxonomyCurrent False False
-- show taxonomy of input
shellShowTaxonomy :: String -> Sh CMDLState ()
shellShowTaxonomy 
 = shellComWith cShowTaxonomy False False
-- show concept of selection
shellShowConceptCurrent :: Sh CMDLState ()
shellShowConceptCurrent
 = shellComWithout cShowConceptCurrent False False
-- show concept of input
shellShowConcept :: String -> Sh CMDLState ()
shellShowConcept 
 = shellComWith cShowConcept False False
-- show node number of input
shellNodeNumber :: String -> Sh CMDLState ()
shellNodeNumber
 = shellComWith cNodeNumber False False
-- print the name of all edges 
shellEdges :: Sh CMDLState ()
shellEdges 
 = shellComWithout cEdges False False
-- print the name of all nodes
shellNodes :: Sh CMDLState ()
shellNodes
 = shellComWithout cNodes False False
-- draw graph
shellDisplayGraph :: Sh CMDLState ()
shellDisplayGraph
 = shellComWithout cDisplayGraph False False

-- show list of all goals(i.e. prints their name)
cShowDgGoals :: CMDLState -> IO CMDLState
cShowDgGoals state
 = case devGraphState state of
    -- nothing to print
    Nothing -> return state
    Just dgState ->
     do 
     -- compute list of node goals
     let nodeGoals=map(\x->case x of
                           (_,DGNode t _ _ _ _ _ _) ->
                            showName t
                           (_,DGRef t _ _ _ _ _) ->
                            showName t)$getAllGoalNodes 
                                         state dgState
         -- list of all nodes                    
         ls  = getAllNodes dgState
         lsE = getAllEdges dgState
         lsGE= getAllGoalEdges dgState
         -- list of all goal edge names
         edgeGoals = createEdgeNames ls lsE lsGE 
     -- print sorted version of the list                   
     prettyPrintList $ sort (nodeGoals++edgeGoals) 
     return state


-- local function that computes the theory of a node but it
-- keeps only the goal theory
getGoalThS :: Int -> CMDLState -> [String]
getGoalThS x state
 = case getTh x state of
    Nothing -> []
    Just th ->
      let nwth = case th of
                  G_theory x1 x2 x3 thSens x4 ->
                    G_theory x1 x2 x3 
                       (OMap.filter (\s-> (not(isAxiom s)) &&
                                          (not(isProvenSenStatus s)))
                       thSens) x4
      in [showDoc nwth "\n"]

--local function that computes the theory of a node 
--that takes into consideration translated theories in 
--the selection too and returns the theory as a string
getThS :: Int -> CMDLState -> [String]
getThS x state
 = case getTh x state of
    Nothing -> []
    Just th -> [showDoc th "\n"]
 

-- show theory of all goals
cShowTheoryGoals :: String -> CMDLState -> IO CMDLState
cShowTheoryGoals input state
 = case devGraphState state of
    --nothing to print
    Nothing -> return state
    Just dgState ->
     do 
     -- compute the input nodes
     let (nds,_,_,errs) = decomposeIntoGoals input
     prettyPrintErrList errs
     case nds of
      [] -> return state
      _  ->
       do
       --list of all nodes
       let lsNodes = getAllNodes dgState
           -- list of input nodes
           (errs',listNodes) = obtainNodeList nds lsNodes
           -- list of all goal theories
           nodeTh = concatMap (\x->case x of
                                  (n,_) ->getGoalThS n state
                                  ) $ listNodes 
       prettyPrintErrList errs'
       prettyPrintList nodeTh
       return state

cShowNodeUGoals :: String -> CMDLState -> IO CMDLState
cShowNodeUGoals input state
 = case devGraphState state of
    --nothing to print
    Nothing -> return state
    Just dgState ->
     do 
     -- compute input nodes
     let (nds,_,_,errs) = decomposeIntoGoals input
     prettyPrintErrList errs
     case nds of
      [] -> return state
      _  -> 
       do
       -- list of all nodes
       let lsNodes = getAllNodes dgState
           -- list of input nodes
           (errs',listNodes) = obtainNodeList nds lsNodes
           -- list of all goal names
           goalNames = 
             concatMap (\x ->case x of
                              (n,_) -> case getTh n state of
                                        Nothing -> []
                                        Just th->
                                         case th of
                                          G_theory _ _ _ sens _->
                                           OMap.keys $ 
                                           OMap.filter 
                                           (\s -> (not $ isAxiom s) &&
                                           (not $ isProvenSenStatus s))
                                           sens) listNodes
       prettyPrintErrList errs'
       prettyPrintList goalNames
       return state

cShowNodeUGoalsCurrent :: CMDLState -> IO CMDLState
cShowNodeUGoalsCurrent state
 = case proveState state of
    Nothing -> return state
    Just pState ->
     do
      let glls = concatMap (\(Element _ nb) ->
                              case getTh nb state of
                               Nothing -> []
                               Just th ->
                                case th of 
                                 G_theory _ _ _ sens _ ->
                                   OMap.keys $
                                   OMap.filter
                                   (\s -> (not $ isAxiom s) &&
                                   (not $ isProvenSenStatus s))
                                   sens) $ elements pState
      prettyPrintList glls
      return state


cShowNodePGoals :: String -> CMDLState -> IO CMDLState
cShowNodePGoals input state
 = case devGraphState state of
    Nothing -> return state
    Just dgState ->
     do
     let (nds,_,_,errs) = decomposeIntoGoals input
     prettyPrintErrList errs
     case nds of
      [] -> return state
      _  ->
       do
        let lsNodes = getAllNodes dgState
            (errs',listNodes) = obtainNodeList nds lsNodes
            goalNames = 
             concatMap (\x -> case x of
                               (n,_) -> case getTh n state of
                                         Nothing -> []
                                         Just th ->
                                          case th of
                                           G_theory _ _ _ sens _ ->
                                            OMap.keys $
                                            OMap.filter
                                            (\s -> (not $ isAxiom s)&&
                                            (isProvenSenStatus s))
                                            sens) listNodes
        prettyPrintErrList errs'
        prettyPrintList goalNames
        return state

cShowNodeAxioms :: String -> CMDLState -> IO CMDLState 
cShowNodeAxioms input state 
 = case devGraphState state of
    Nothing -> return state 
    Just dgState ->
     do 
     let (nds,_,_,errs) = decomposeIntoGoals input
     prettyPrintErrList errs
     case nds of
      [] -> return state
      _ ->
       do
       let lsNodes = getAllNodes dgState
           (errs',listNodes) = obtainNodeList nds lsNodes
           goalNames = 
            concatMap (\x ->case x of
                             (n,_)-> case getTh n state of
                                      Nothing -> []
                                      Just th ->
                                       case th of
                                        G_theory _ _ _ sens _->
                                         OMap.keys $ OMap.filter 
                                         isAxiom sens) listNodes
       prettyPrintErrList errs'
       prettyPrintList goalNames
       return state


cShowNodePGoalsCurrent :: CMDLState -> IO CMDLState
cShowNodePGoalsCurrent state
 = case proveState state of
    Nothing -> return state
    Just pState ->
     do
      let glls = concatMap (\(Element _ nb) ->
                              case getTh nb state of
                               Nothing -> []
                               Just th ->
                                case th of
                                 G_theory _ _ _ sens _ ->
                                   OMap.keys $
                                   OMap.filter
                                   (\s -> (not $ isAxiom s) &&
                                   (isProvenSenStatus s)) sens) $
                                   elements pState
      prettyPrintList glls
      return state


cShowNodeAxiomsCurrent :: CMDLState -> IO CMDLState
cShowNodeAxiomsCurrent state
 = case proveState state of
    Nothing -> return state
    Just pState ->
     do
      let glls = concatMap (\(Element _ nb) ->
                              case getTh nb state of
                               Nothing -> []
                               Just th ->
                                case th of
                                 G_theory _ _ _ sens _ ->
                                   OMap.keys $
                                   OMap.filter isAxiom sens) $
                                   elements pState
      prettyPrintList glls
      return state

cShowTheoryGoalsCurrent :: CMDLState -> IO CMDLState
cShowTheoryGoalsCurrent state
 = case proveState state of
     Nothing -> return state
     Just pState ->
      do
       -- list of selected theories
       let thls = concatMap (\(Element _ nb) ->
                              getGoalThS nb state)
                    $ elements pState
       prettyPrintList thls
       return state

-- show theory of selection
cShowTheoryCurrent :: CMDLState -> IO CMDLState
cShowTheoryCurrent state
 = case proveState state of
    Nothing -> return state
    Just pState ->
     do
      -- list of selected theories
      let thls = concatMap (\(Element _ nb) ->
                              getThS nb state)
                     $ elements pState
      prettyPrintList thls
      return state
 
-- show theory of input nodes
cShowTheory :: String -> CMDLState -> IO CMDLState
cShowTheory input state
 = case devGraphState state of
    Nothing -> return state
    Just dgState -> do
     -- compute the input nodes
     let (nds,_,_,errs) = decomposeIntoGoals input
     prettyPrintErrList errs
     case nds of
       [] -> return state
       _  ->
        do
        --list of all nodes
        let lsNodes = getAllNodes dgState
            -- list of input nodes
            (errs',listNodes) = obtainNodeList nds lsNodes
            -- list of theories that need to be printed
            thls =concatMap(\(x,_)->getThS x state) listNodes
         -- sort before printing !?    
        prettyPrintErrList errs'
        prettyPrintList thls
        return state
         

-- | Given a node it returns the information that needs to 
-- be printed as a string
showNodeInfo::CMDLState -> LNode DGNodeLab -> String 
showNodeInfo state (nb,nd)
 =let
    -- node name
      name'= case nd of
              (DGNode name _ _ _ _ _ _)->
                 "dgn_name :"++(showName name)++"\n"
              (DGRef name _ _ _ _ _) ->
                 "dgn_name :"++(showName name)++"\n"
      -- origin of the node
      orig'= case nd of
              (DGNode _ _ _ _ orig _ _) ->
                  "dgn_orig :"++(show orig)++"\n"
              _ ->
                  "dgn_orig : no origin (ref node)"
      -- conservativity annotations
      th = getTh nb state
  in 
   case th of 
    Nothing ->name' ++ orig'++"Theory could not be evaluated\n"
    Just t@(G_theory x y _ thSens _) ->
     let
      -- find out the sublogic of the theory if we found
      -- a theory
      sublog = "   sublogic :"++(show 
                              $ sublogicOfTh t)++"\n"
      -- compute the number of axioms by counting the
      -- number of symbols of the signature !?
      nbAxm = "   number of axioms :"++(show $ OMap.size $
                                   OMap.filter isAxiom thSens) ++"\n"
      -- compute the number of symbols as the number of
      -- sentences that are axioms in the senstatus of the
      -- theory
      nbSym = "   number of symbols :"++(show $
                    Set.size $ sym_of x y)++ "\n"
      -- compute the number of proven theorems as the 
      -- number of sentences that have no theorem status
      -- left
      nbThm = let n'=OMap.size $ OMap.filter (\s -> (not (isAxiom s)) 
                      && (isProvenSenStatus s)) thSens
              in "   number of proven theorems :"++
                     (show n') ++ "\n"
      -- compute the number of unproven theorems as the
      -- sentences that have something in their theorem 
      -- status
      nbUThm = let n'=OMap.size $ OMap.filter(\s -> (not (isAxiom s))
                       && (not (isProvenSenStatus s))) thSens
               in "   number of unproven theorems :"++
                     (show n') ++ "\n"
      -- compute the final theory (i.e.just add partial
      -- results obtained before (sublogic, nbAxm..)
      th' = "dgl_theory :\n"++ sublog ++ nbAxm
                         ++ nbSym ++ nbThm ++ nbUThm
     in name' ++ orig' ++ th'
 

-- | Given and edge it returns the information that needs to 
--be printed as a string
showEdgeInfo::CMDLState -> LEdge DGLinkLab -> String
showEdgeInfo state (x,y,dglab@(DGLink morp _ org _ ) )
 =case devGraphState state of
   Nothing -> ""
   Just dgS ->
    let 
     ls = getAllNodes dgS
     nameOf x' l =case find (\(nb,_)->nb==x') l of
                   Nothing->"Unknown node"
                   Just (_,DGNode t _ _ _ _ _ _) ->
                    showName t
                   Just (_,DGRef t _ _ _ _ _) ->
                    showName t
     name = "dgl_name :"++(nameOf x ls)++" -> "++
               (nameOf y ls) ++ "\n"
     orig = "dgl_origin :"++(show $ org)++"\n"
     homog= "dgl_homogeneous :"++ (show $ isHomogeneous morp)
                          ++ "\n"
     ltype= "dgl_type :"++ 
             (case getDGLinkType dglab of
               "globaldef"->"global definition"
               "def"->"local definition"
               "hidingef"->"hiding definition"
               "hetdef"->"het definitions"
               "proventhm"->"global proven theorem"
               "unproventhm"->"global unproven theorem"
               "localproventhm"->"local proven theorem"
               "localunproventhm"->"local unproven theorem"
               "hetproventhm"->"het global proven theorem"
               "hetunproventhm"->"het global unproven theorem"
               "hetlocalproventhm"->"het local proven theorem"
               "hetlocalunproventhm"->"het local unproven"++
                                            "theorem"
               "unprovenhidingthm"->"unproven hiding theorem"
               "provenhidingthm"->"proven hiding theorem"
               _                ->"unknown type"
                ) ++ "\n"
    in name++orig++homog++ltype              


 -- show all information of selection
cInfoCurrent::CMDLState -> IO CMDLState
cInfoCurrent state
 = case proveState state of
    -- nothing selected
    Nothing -> return state
    Just ps ->
     case devGraphState state of
      Nothing -> return state
      Just dgS->
       do
       -- get node by number
       let getNNb x l' = case find (\y->case y of
                                      (nb,_) -> nb==x
                                      ) l' of
                               Nothing -> []
                               Just sm -> [sm]
           -- get all nodes
           ls = getAllNodes dgS
           -- get node numbers of selected nodes
           nodesNb = map (\x -> case x of
                                 Element _ z -> z) 
                                    $ elements ps
           -- obtain the selected nodes
           selN = concatMap (\x-> getNNb x ls) nodesNb
       prettyPrintList 
             $ map (\x-> showNodeInfo state x) selN
       return state

-- show all information of input
cInfo::String -> CMDLState -> IO CMDLState
cInfo input state
 = case devGraphState state of
    -- error message
    Nothing -> return state {
                       errorMsg = "No library loaded"
                        }
    Just dgS -> do
     let (nds,edg,nbEdg,errs) = decomposeIntoGoals input
     prettyPrintErrList errs
     case (nds,edg,nbEdg) of
      ([],[],[]) -> return state {
                            errorMsg = "Nothing from the input "
                                       ++"could be processed"
                            }
      (_,_,_) ->
       do
        let lsNodes = getAllNodes dgS
            lsEdges = getAllEdges dgS
            (errs'',listEdges) = obtainEdgeList edg nbEdg lsNodes
                             lsEdges
            (errs',listNodes) = obtainNodeList nds lsNodes
            strsNode = map (\x -> showNodeInfo state x) 
                               listNodes
            strsEdge = map (\x -> showEdgeInfo state x)
                               listEdges
        prettyPrintErrList errs'
        prettyPrintErrList errs''
        prettyPrintList (strsNode ++ strsEdge) 
        return state



taxoShowGeneric:: TaxoGraphKind -> CMDLState 
                      -> [LNode DGNodeLab] -> IO()
taxoShowGeneric kind state ls
 = case ls of
#ifdef UNI_PACKAGE
    (nb,nlab):ll ->
     case devGraphState state of
      Nothing -> return ()
      Just _ ->
       do
       case getTh nb state of
       -- the theory was computed
        Just th ->
         do
          -- display graph
          graph <- displayGraph kind 
                    (showName $ dgn_name nlab) th
          case graph of
           -- if successfully displayed sync the two threads
           -- so that one does not loose control on the 
           -- interface while the graph is displayed
           Just g -> 
            do sync (destroyed g) 
               -- go to next
               taxoShowGeneric kind state ll
           Nothing ->
               -- graph was not displayed, then just 
               -- go to next
               taxoShowGeneric kind state ll
        -- theory couldn't be computed so just go next
        _ -> taxoShowGeneric kind state ll                
#endif
    _ -> return ()

-- show taxonomy of selection
cShowTaxonomyCurrent::CMDLState -> IO CMDLState
cShowTaxonomyCurrent state
 = case proveState state of
    -- nothing selected
    Nothing -> return state
    -- else
    Just ps ->
     case devGraphState state of
      Nothing -> return state
      Just dgS->
       do
     -- get node by number
       let getNNb x ks = case find (\y -> case y of
                                       (nb,_) -> nb==x
                                       ) ks of
                           Nothing -> []
                           Just sm -> [sm]
           -- get all nodes                            
           ls = getAllNodes dgS
           -- get node numbers of selected nodes
           nodesNb = map (\x -> case x of 
                                 Element _ z ->z) 
                                     $ elements ps
           -- obtain the selected nodes
           selN = concatMap (\x-> getNNb x ls) nodesNb
       taxoShowGeneric KSubsort state selN
       return state

-- show taxonomy of input
cShowTaxonomy::String -> CMDLState -> IO CMDLState
cShowTaxonomy input state
 = case devGraphState state of
    -- nothing to print
    Nothing -> return state
    Just dgS -> do
     let (nds,_,_,errs) = decomposeIntoGoals input
     prettyPrintErrList errs
     case nds of
      [] -> return state
      _  ->
       do
        -- list of all nodes
        let ls = getAllNodes dgS
        -- list of input nodes
            (errs',lsNodes) = obtainNodeList nds ls
        prettyPrintErrList errs'
        taxoShowGeneric KSubsort state lsNodes
        return state

-- show concept of selection
cShowConceptCurrent::CMDLState -> IO CMDLState
cShowConceptCurrent state
 = case proveState state of
    -- nothing selected
    Nothing -> return state
    -- else
    Just ps ->
     case devGraphState state of
      Nothing -> return state
      Just dgS->
       do
     -- get node by number
       let getNNb x ks = case find (\y -> case y of
                                       (nb,_) -> nb==x
                                       ) ks of
                           Nothing -> []
                           Just sm -> [sm]
           -- get all nodes                            
           ls = getAllNodes dgS
           -- get node numbers of selected nodes
           nodesNb = map (\x -> case x of 
                                 Element _ z -> z) 
                                    $ elements ps
           -- obtain the selected nodes
           selN = concatMap (\x-> getNNb x ls) nodesNb
       taxoShowGeneric KConcept state selN
       return state


-- show concept of input
cShowConcept::String -> CMDLState -> IO CMDLState
cShowConcept input state
 = case devGraphState state of
    -- nothing to print
    Nothing -> return state
    Just dgS -> do
     let (nds,_,_,errs) = decomposeIntoGoals input
     prettyPrintErrList errs
     case nds of
      [] -> return state
      _  ->
       do
        -- list of all nodes
        let ls = getAllNodes dgS
        -- list of input nodes
            (errs',lsNodes) = obtainNodeList nds ls
        prettyPrintErrList errs'    
        taxoShowGeneric KSubsort state lsNodes
        return state



-- show node number of input
cNodeNumber::String -> CMDLState -> IO CMDLState
cNodeNumber input state
 = case devGraphState state of
    Nothing -> return state
    Just dgState -> do
     -- compute the input nodes
     let (nds,_,_,errs) = decomposeIntoGoals input
     prettyPrintErrList errs
     case nds of
      [] -> return state
      _  ->
       do
        -- list og all nodes
        let lsNodes = getAllNodes dgState
        -- list of input nodes
            (errs',listNodes)=obtainNodeList nds lsNodes
        -- nodes numbers to print
            ls = map(\x -> case x of
                            (n,DGNode t _ _ _ _ _ _) ->
                             (showName t)++" is node number " 
                                  ++ (show n)
                            (n,DGRef t _ _ _ _ _) ->
                             (showName t)++" is node number "
                                  ++ (show n) ) listNodes
        prettyPrintErrList errs'                          
        prettyPrintList ls
        return state

-- print the name of all edges 
cEdges::CMDLState -> IO CMDLState
cEdges state
 = case devGraphState state of 
    Nothing -> return state
    Just dgState ->
     do
      -- list of all nodes
      let lsNodes = getAllNodes dgState
          -- compute all edges names  
          lsEdg = getAllEdges dgState
          lsEdges = createEdgeNames lsNodes lsEdg lsEdg
      -- print edge list in a sorted fashion
      prettyPrintList $ sort lsEdges
      return state

-- print the name of all nodes
cNodes::CMDLState -> IO CMDLState
cNodes state
 = case devGraphState state of
    -- no library loaded, so nothing to print
    Nothing -> return state
    Just dgState ->
     do
     -- compute the list of node names
     let ls = map (\x-> case x of
                         (_,DGNode t _ _ _ _ _ _) ->
                          showName t
                         (_,DGRef t _ _ _ _ _) ->
                          showName t) $ getAllNodes dgState
     -- print a sorted version of it
     prettyPrintList $ sort ls
     return state


-- draw graph
cDisplayGraph::CMDLState -> IO CMDLState
cDisplayGraph state
 = case devGraphState state of
#ifdef UNI_PACKAGE
    Just dgState ->
     do
      -- obtain the name of the last loaded library for
      -- documentation/debugging reasons
      let filename = reverse $ drop 2 $ reverse 
                      $ prompter state
      showGraph filename defaultHetcatsOpts ( Just 
                   (ln dgState, libEnv dgState))
      return state
#endif
   -- no development graph present
    _ -> return state
    

