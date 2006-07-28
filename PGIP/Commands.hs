{- |
Module      :$Header$
Copyright   : uni-bremen and Razvan Pascanu
Licence     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@iu-bremen.de
Stability   : provisional
Portability : portable

Function that executes the script commands together with the datatypes used.

 TODO :
      - add comments
      - implement the rest of the functions 
      - delete the test function
-} 

module PGIP.Commands where

import Syntax.AS_Library
import Static.AnalysisLibrary
import Static.DevGraph
import Driver.Options
import Common.Utils
import Proofs.Automatic
import Proofs.Global
import Proofs.Local
import Proofs.Composition
import Proofs.HideTheoremShift
import Proofs.TheoremHideShift
import Proofs.EdgeUtils
import Proofs.InferBasic
import Common.Id
import Common.DocUtils
import Common.Result
import Common.Taxonomy
import GUI.Taxonomy
import Data.Maybe
import Data.Graph.Inductive.Graph
import Comorphisms.LogicGraph
import PGIP.Common
--import Proofs.InferBasic




test::([ScriptCommandParameters])->IO()
test (ls) = putStrLn $ show ls
               

commandUse::[ScriptCommandParameters]->IO [CmdInterpreterStatus]
commandUse ls 
            = case ls of
                (Path list):_ -> do
                                  let file = joinWith '/' list
                                  let opts = defaultHetcatsOpts
                                  result<- anaLib opts file
                                  case result of
                                      Just (name,env) -> do
                                                           let ls=createAllGoalsList name env
                                                           return ((Env name env):(AllGraphGoals ls):[] )
                                      Nothing ->  return [(OutputErr "Couldn't load the file specified")]
                _             -> return [(OutputErr "Wrong parameter")]

commandDgAllAuto::[CmdInterpreterStatus] -> [CmdInterpreterStatus]
commandDgAllAuto arg
                 = case arg of
                      (Env x y):_   -> let result= automatic x y 
                                           newGoalList = createAllGoalsList x result
                                       in  (Env x result):(AllGraphGoals newGoalList):[]
                      _:l           -> commandDgAllAuto l
                      []            -> [(OutputErr "Wrong parameter")]

commandDgAuto :: ([ScriptCommandParameters],[CmdInterpreterStatus]) -> [CmdInterpreterStatus]
commandDgAuto (param,status)
       = case status of
           (Env ln libEnv):l -> case l of
                                 (AllGraphGoals allGoals):_ ->case param of
                                                                (Goals ls):_ -> let ll = getEdgeList $ getGoalList ls allGoals
                                                                                    result = automaticFromList ln ll libEnv
                                                                                    newGoalList = createAllGoalsList ln result
                                                                                in (Env ln result):(AllGraphGoals newGoalList):[]
                                                                _            -> [(OutputErr "Wrong parameters")]
                                 _:list -> commandDgAuto (param, (Env ln libEnv):list)
           (AllGraphGoals allGoals):l -> case l of
                                          (Env ln libEnv):_ -> case param of 
                                                                 (Goals ls):_ ->let ll = getEdgeList $ getGoalList ls allGoals
                                                                                    result = automaticFromList ln ll libEnv
                                                                                    newGoalList = createAllGoalsList ln result
                                                                                in (Env ln result):(AllGraphGoals newGoalList):[]
                                                                 _ -> [(OutputErr "Wrong parameters")]
                                          _:list -> commandDgAuto(param, (AllGraphGoals allGoals):list)
           _:l               -> commandDgAuto (param, l)
           []                -> [(OutputErr "Wrong parameters")]

commandDgGlobSubsume::([ScriptCommandParameters],[CmdInterpreterStatus]) -> [CmdInterpreterStatus]
commandDgGlobSubsume (param,status)
     = case status of
        (Env ln libEnv):l  -> case l of 
                                (AllGraphGoals allGoals):_ -> case param of
                                                               (Goals ls):_ -> let ll = getEdgeList $ getGoalList ls allGoals
                                                                                   result = globSubsumeFromList ln ll  libEnv 
                                                                                   newGoalList = createAllGoalsList ln result
                                                                               in (Env ln result):(AllGraphGoals newGoalList):[]
                                                               _            -> [(OutputErr "Wrong parameters")]
                                _:list -> commandDgGlobSubsume(param, (Env ln libEnv):list)
        (AllGraphGoals allGoals):l -> case l of 
                                       (Env ln libEnv):_ -> case param of
                                                              (Goals ls):_ -> let ll= getEdgeList $ getGoalList ls allGoals
                                                                                  result = globSubsumeFromList ln ll libEnv
                                                                                  newGoalList = createAllGoalsList ln result
                                                                              in (Env ln result):(AllGraphGoals newGoalList):[]
                                                              _            -> [(OutputErr "Wrong parameters")]
                                       _:list -> commandDgGlobSubsume(param, (AllGraphGoals allGoals):list)
        _:l                -> commandDgGlobSubsume (param,l)
        []                 -> [(OutputErr "Wrong parameters")]



commandDgAllGlobSubsume::[CmdInterpreterStatus] -> [CmdInterpreterStatus]
commandDgAllGlobSubsume arg
                          = case arg of
                               (Env x y):_  -> let result =(globSubsume x) y 
                                                   newGoalList = createAllGoalsList x result
                                               in  (Env x result):(AllGraphGoals newGoalList):[]
                               _:l          -> commandDgAllGlobSubsume l
                               []           -> [(OutputErr "Wrong parameters")]

commandDgAllGlobDecomp::[CmdInterpreterStatus] -> [CmdInterpreterStatus]
commandDgAllGlobDecomp arg 
                          = case arg of 
                               (Env x y):_ -> let result= (globDecomp x) y 
                                                  newGoalList = createAllGoalsList x result
                                              in  (Env x result):(AllGraphGoals newGoalList):[]
                               _:l         -> commandDgAllGlobDecomp l
                               []          -> [(OutputErr "Wrong parameters")]


commandDgGlobDecomp :: ([ScriptCommandParameters],[CmdInterpreterStatus]) -> [CmdInterpreterStatus]
commandDgGlobDecomp (param,status) 
      = case status of
         (Env ln libEnv):l  -> case l of 
                                (AllGraphGoals allGoals):_ -> case param of
                                                               (Goals ls):_ -> let ll = getEdgeList $ getGoalList ls allGoals
                                                                                   result = globDecompFromList ln ll  libEnv 
                                                                                   newGoalList = createAllGoalsList ln result
                                                                               in  (Env ln result):(AllGraphGoals newGoalList):[]
                                                               _            -> [(OutputErr "Wrong parameters")]
                                _:list -> commandDgGlobDecomp(param, (Env ln libEnv):list)
         (AllGraphGoals allGoals):l -> case l of 
                                       (Env ln libEnv):_ -> case param of
                                                             (Goals ls):_ -> let ll= getEdgeList $ getGoalList ls allGoals
                                                                                 result = globDecompFromList ln ll libEnv
                                                                                 newGoalList = createAllGoalsList ln result
                                                                             in  (Env ln result):(AllGraphGoals newGoalList):[]
                                                             _            -> [(OutputErr "Wrong parameters")]
                                       _:list -> commandDgGlobDecomp(param, (AllGraphGoals allGoals):list)
         _:l                -> commandDgGlobDecomp (param,l)
         []                 -> [(OutputErr "Wrong parameters")]


commandDgAllLocInfer::[CmdInterpreterStatus] -> [CmdInterpreterStatus]                        
commandDgAllLocInfer arg
                        = case arg of
                             (Env x y):_ -> let result= (localInference x) y
                                                newGoalList = createAllGoalsList x result 
                                            in  (Env x result):(AllGraphGoals newGoalList):[]
                             _:l         -> commandDgAllLocInfer l
                             []          -> [(OutputErr "Wrong parameters")]


commandDgLocInfer::([ScriptCommandParameters],[CmdInterpreterStatus]) -> [CmdInterpreterStatus]
commandDgLocInfer (param,status)
    = case status of
         (Env ln libEnv):l  -> case l of 
                                (AllGraphGoals allGoals):_ -> case param of
                                                               (Goals ls):_ -> let ll = getEdgeList $ getGoalList ls allGoals
                                                                                   result = localInferenceFromList ln ll  libEnv 
                                                                                   newGoalList = createAllGoalsList ln result
                                                                               in (Env ln result):(AllGraphGoals newGoalList):[]
                                                               _            -> [(OutputErr "Wrong parameters")]
                                _:list -> commandDgLocInfer(param, (Env ln libEnv):list)
         (AllGraphGoals allGoals):l -> case l of 
                                       (Env ln libEnv):_ -> case param of
                                                              (Goals ls):_ -> let ll= getEdgeList $ getGoalList ls allGoals
                                                                                  result = localInferenceFromList ln ll libEnv
                                                                                  newGoalList = createAllGoalsList ln result
                                                                              in (Env ln result):(AllGraphGoals newGoalList):[]
                                                              _            -> [(OutputErr "Wrong parameters")]
                                       _:list -> commandDgLocInfer(param, (AllGraphGoals allGoals):list)
         _:l                -> commandDgLocInfer (param,l)
         []                 -> [(OutputErr "Wrong parameters")]


commandDgAllLocDecomp::[CmdInterpreterStatus] -> [CmdInterpreterStatus]
commandDgAllLocDecomp arg
                         = case arg of 
                               (Env x y):l -> let result= (locDecomp x) y 
                                                  newGoalList = createAllGoalsList x result
                                              in  (Env x result):(AllGraphGoals newGoalList):[]
                               _:l         -> commandDgAllLocDecomp l
                               []          -> [(OutputErr "Wrong parameters")]


commandDgLocDecomp::([ScriptCommandParameters], [CmdInterpreterStatus])-> [CmdInterpreterStatus]
commandDgLocDecomp (param,status)
     = case status of
         (Env ln libEnv):l  -> case l of 
                                (AllGraphGoals allGoals):_ -> case param of
                                                               (Goals ls):_ -> let ll = getEdgeList $ getGoalList ls allGoals
                                                                                   result = locDecompFromList ln ll  libEnv 
                                                                                   newGoalList = createAllGoalsList ln result
                                                                               in (Env ln result):(AllGraphGoals newGoalList):[]
                                                               _            -> [(OutputErr "Wrong parameters")]
                                _:list -> commandDgLocDecomp(param, (Env ln libEnv):list)
         (AllGraphGoals allGoals):l -> case l of 
                                       (Env ln libEnv):_ -> case param of
                                                              (Goals ls):_ -> let ll= getEdgeList $ getGoalList ls allGoals
                                                                                  result = locDecompFromList ln ll libEnv
                                                                                  newGoalList = createAllGoalsList ln result
                                                                              in (Env ln result):(AllGraphGoals newGoalList):[]
                                                              _            -> [(OutputErr "Wrong parameters")]
                                       _:list -> commandDgLocDecomp(param, (AllGraphGoals allGoals):list)
         _:l                -> commandDgLocDecomp (param,l)
         []                 -> [(OutputErr "Wrong parameters")]



commandDgComp::([ScriptCommandParameters], [CmdInterpreterStatus]) -> [CmdInterpreterStatus]
commandDgComp (param, status)
     = case status of
         (Env ln libEnv):l  -> case l of 
                                (AllGraphGoals allGoals):_ -> case param of
                                                               (Goals ls):_ -> let ll = getEdgeList $ getGoalList ls allGoals
                                                                                   result = compositionFromList ln ll  libEnv 
                                                                                   newGoalList = createAllGoalsList ln result
                                                                               in (Env ln result):(AllGraphGoals newGoalList):[]
                                                               _            -> [(OutputErr "Wrong parameters")]
                                _:list -> commandDgComp(param, (Env ln libEnv):list)
         (AllGraphGoals allGoals):l -> case l of 
                                       (Env ln libEnv):_ -> case param of
                                                              (Goals ls):_ -> let ll= getEdgeList $ getGoalList ls allGoals
                                                                                  result = compositionFromList ln ll libEnv
                                                                                  newGoalList = createAllGoalsList ln result
                                                                              in (Env ln result):(AllGraphGoals newGoalList):[]
                                                              _            -> [(OutputErr "Wrong parameters")]
                                       _:list -> commandDgComp(param, (AllGraphGoals allGoals):list)
         _:l                -> commandDgComp (param,l)
         []                 -> [(OutputErr "Wrong parameters")]




commandDgAllComp::[CmdInterpreterStatus] -> [CmdInterpreterStatus]
commandDgAllComp arg 
                    = case arg of
                           (Env x y):_ -> let result= (composition x) y 
                                              newGoalList = createAllGoalsList x result
                                          in  (Env x result):(AllGraphGoals newGoalList):[]
                           _:l         -> commandDgAllComp l
                           []          -> [(OutputErr "Wrong parameters")]

commandDgCompNew::([ScriptCommandParameters],[CmdInterpreterStatus]) -> [CmdInterpreterStatus]
commandDgCompNew (param, status)
     = case status of
         (Env ln libEnv):l  -> case l of 
                                (AllGraphGoals allGoals):_ -> case param of
                                                               (Goals ls):_ -> let ll = getEdgeList $ getGoalList ls allGoals
                                                                                   result = compositionCreatingEdgesFromList ln ll  libEnv 
                                                                                   newGoalList = createAllGoalsList ln result
                                                                               in (Env ln result):(AllGraphGoals newGoalList):[]
                                                               _            -> [(OutputErr "Wrong parameters")]
                                _:list -> commandDgCompNew(param, (Env ln libEnv):list)
         (AllGraphGoals allGoals):l -> case l of 
                                       (Env ln libEnv):_ -> case param of
                                                              (Goals ls):_ -> let ll= getEdgeList $ getGoalList ls allGoals
                                                                                  result = compositionCreatingEdgesFromList ln ll libEnv
                                                                                  newGoalList = createAllGoalsList ln result
                                                                              in (Env ln result):(AllGraphGoals newGoalList):[]
                                                              _            -> [(OutputErr "Wrong parameters")]
                                       _:list -> commandDgCompNew(param, (AllGraphGoals allGoals):list)
         _:l                -> commandDgCompNew (param,l)
         []                 -> [(OutputErr "Wrong parameters")]


 

commandDgAllCompNew::[CmdInterpreterStatus] -> [CmdInterpreterStatus]
commandDgAllCompNew arg
                      = case arg of
                             (Env x y):_ -> let result=(compositionCreatingEdges x) y
                                                newGoalList = createAllGoalsList x result
                                            in  (Env x result):(AllGraphGoals newGoalList):[]
                             _:l         -> commandDgAllCompNew l
                             []          -> [(OutputErr "Wrong parameters")]

commandDgHideThm::([ScriptCommandParameters],[CmdInterpreterStatus]) -> [CmdInterpreterStatus]
commandDgHideThm (param, status)
     = case status of
         (Env ln libEnv):l  -> case l of 
                                (AllGraphGoals allGoals):_ -> case param of
                                                               (Goals ls):_ -> let ll = getEdgeList $ getGoalList ls allGoals
                                                                                   result = automaticHideTheoremShiftFromList ln ll  libEnv 
                                                                                   newGoalList = createAllGoalsList ln result
                                                                               in (Env ln result):(AllGraphGoals newGoalList):[]
                                                               _            -> [(OutputErr "Wrong parameters")]
                                _:list -> commandDgHideThm(param, (Env ln libEnv):list)
         (AllGraphGoals allGoals):l -> case l of 
                                       (Env ln libEnv):_ -> case param of
                                                              (Goals ls):_ -> let ll= getEdgeList $ getGoalList ls allGoals
                                                                                  result = automaticHideTheoremShiftFromList ln ll libEnv
                                                                                  newGoalList = createAllGoalsList ln result
                                                                              in (Env ln result):(AllGraphGoals newGoalList):[]
                                                              _            -> [(OutputErr "Wrong parameters")]
                                       _:list -> commandDgHideThm(param, (AllGraphGoals allGoals):list)
         _:l                -> commandDgHideThm (param,l)
         []                 -> [(OutputErr "Wrong parameters")]



commandDgAllHideThm::[CmdInterpreterStatus] -> [CmdInterpreterStatus]
commandDgAllHideThm arg
                      = case arg of
                             (Env x y):_ -> let result= (automaticHideTheoremShift x) y 
                                                newGoalList = createAllGoalsList x result
                                            in  (Env x result):(AllGraphGoals newGoalList):[]
                             _:l         -> commandDgAllHideThm l
                             []          -> [(OutputErr "Wrong parameters")]

commandDgAllThmHide::[CmdInterpreterStatus] -> [CmdInterpreterStatus]
commandDgAllThmHide arg
                       = case arg of
                              (Env x y):_ -> let result=(theoremHideShift x) y 
                                                 newGoalList = createAllGoalsList x result
                                             in  (Env x result):(AllGraphGoals newGoalList):[]
                              _:l         -> commandDgAllThmHide l
                              []          -> [(OutputErr "Wrong parameters")]


commandDgAllInferBasic::[CmdInterpreterStatus] -> [CmdInterpreterStatus]
commandDgAllInferBasic arg
                        = case arg of
                               (AllGraphGoals allGoals):_ -> [Selected allGoals] 
                               _:l         -> commandDgAllInferBasic l
                               []          -> [(OutputErr "Wrong parameters")]



commandDgInferBasic::([ScriptCommandParameters],[CmdInterpreterStatus]) -> [CmdInterpreterStatus]
commandDgInferBasic (param, status)
      = case status of
          (AllGraphGoals allGoals):_ -> case param of
                                 (Goals ls):_ -> let ll = getGoalList ls allGoals
                                                 in  (Selected ll):[] 
                                 _            -> [(OutputErr "Wrong parameters")]
          _:l               -> commandDgInferBasic (param, l)
          []                -> [(OutputErr "Wrong parameters")]
                                        

commandTranslate::([ScriptCommandParameters],[CmdInterpreterStatus]) -> [CmdInterpreterStatus]
commandTranslate (param, _)
      = case param of
                 (ParsedComorphism ls):_ -> [(Comorphism ls)] 
                 _                       -> [(OutputErr "Wrong parameters")]

commandProver::([ScriptCommandParameters],[CmdInterpreterStatus]) -> [CmdInterpreterStatus]
commandProver (param, _)
       = case param of
                 (Prover ls ):_      -> [(ProverUsed ls)]
                 _                   -> [(OutputErr "Wrong parameters")]

commandShowDgGoals::[CmdInterpreterStatus]-> IO()
commandShowDgGoals  arg
              = do
                 case arg of
                      (AllGraphGoals allGoals):_ -> printNodeInfoFromList allGoals--putStr ("Goals:" ++ (show allGoals))
                      _:l -> commandShowDgGoals l
                      []  -> putStr "Error, no goal list found!\n "


commandShowTheory::[CmdInterpreterStatus] -> IO()
commandShowTheory arg
             = case arg of 
                      (AllGraphGoals allGoals):_ -> printNodeTheoryFromList allGoals
                      _:l                        -> commandShowNodeTheory l
                      []                         -> putStr "Error, no goal list found ! \n"


commandShowNodeTheory::[CmdInterpreterStatus] -> IO()
commandShowNodeTheory arg
             = case arg of 
                      (Selected xx):_ -> printNodeTheoryFromList xx 
                      _:l                        -> commandShowNodeTheory l
                      []                         -> putStr "Error, no nodes selected ! \n"

commandShowNodeInfo :: [CmdInterpreterStatus] -> IO()
commandShowNodeInfo arg
                = case arg of
                      (Selected xx):_ -> printNodeInfoFromList xx
                      _:l             -> commandShowNodeInfo l
                      []              -> putStr "Error, no nodes selected ! \n"

commandShowNodeConcept :: [CmdInterpreterStatus] -> IO()
commandShowNodeConcept arg
                  = case arg of 
                       (Selected xx):_ -> printNodeTaxonomyFromList KConcept xx
                       _:l             -> commandShowNodeConcept l
                       []              -> putStr "Error, no nodes selected ! \n"

commandShowNodeTaxonomy ::[CmdInterpreterStatus] -> IO()
commandShowNodeTaxonomy arg
                 = case arg of
                       (Selected xx):_ -> printNodeTaxonomyFromList KSubsort xx
                       _:l             -> commandShowNodeTaxonomy l
                       []              -> putStr "Error, no nodes selected !\n"


commandProveAll :: [CmdInterpreterStatus]->IO [CmdInterpreterStatus]
commandProveAll arg =
           case arg of
                (Env ln libEnv):l -> case l of
                                       (AllGraphGoals ls):_ -> do 
                                                                result <- proveNodes ls ln libEnv
                                                                let newGoalList = createAllGoalsList ln result
                                                                return  ((AllGraphGoals newGoalList):(Env ln result):[])
                                       _:ll                 -> commandProveAll ((Env ln libEnv):ll)
                                       _                    -> return [OutputErr "Wrong parameters"]
                (AllGraphGoals ls):l -> case l of
                                          (Env ln libEnv):_ -> do
                                                                result <- proveNodes ls ln libEnv
                                                                let newGoalList = createAllGoalsList ln result
                                                                return  ((AllGraphGoals newGoalList):(Env ln result):[])
                                          _:ll              -> commandProveAll ((AllGraphGoals ls):ll)
                                          _                 -> return [OutputErr "Wrong parameters"]
                _:l                -> commandProveAll l
                _                  -> return [OutputErr "Wrong parameters"]
