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
import Common.Id
import Data.Maybe
import Data.Graph.Inductive.Graph

--import Proofs.InferBasic


data GOAL = 
   Node         Id
 | Edge         Id   Id
 | LabeledEdge  Id   Int     Id
 deriving (Eq,Show)


data ScriptCommandParameters =
   Path                         [String] 
 | Formula                       Id 
 | Prover                        Id
 | Goals                         [GOAL]
 | ParsedComorphism             [Id]
 | AxiomSelectionWith           [Id]
 | AxiomSelectionExcluding      [Id]
 | Formulas                     [Id]
 | ProofScript                   String
 | ParamErr                      String
 | NoParam
 deriving (Eq,Show)

data CmdInterpreterStatus = 
   OutputErr  String
 | CmdInitialState
 | Env     LIB_NAME LibEnv


data CmdInterpreterStatusID =
   EnvID
 
data CommandFunctionsAndParameters=
   CommandParam        ([ScriptCommandParameters]->IO CmdInterpreterStatus) [ScriptCommandParameters] 
 | CommandParamStatus  (([ScriptCommandParameters],CmdInterpreterStatus)-> CmdInterpreterStatus) [ScriptCommandParameters] CmdInterpreterStatusID 
 | CommandStatus       (CmdInterpreterStatus -> CmdInterpreterStatus) CmdInterpreterStatusID
 | CommandTest         ([ScriptCommandParameters]->IO())  [ScriptCommandParameters]
 | CommandError



test::([ScriptCommandParameters])->IO()
test (ls) = putStrLn $ show ls
               

commandUse::[ScriptCommandParameters]->IO CmdInterpreterStatus
commandUse ls 
            = case ls of
                (Path list):_ -> do
                                  let file = joinWith '/' list
                                  let opts = defaultHetcatsOpts
                                  result<- anaLib opts file
                                  case result of
                                      Just (name,env) ->  return (Env name env) 
                                      Nothing ->  return (OutputErr "Couldn't load the file specified")
                _             -> return (OutputErr "Wrong parameter") 

commandDgAllAuto::CmdInterpreterStatus -> CmdInterpreterStatus
commandDgAllAuto arg
                 = case arg of
                      (Env x y) -> let result= (automatic x) y in
                                       (Env x result)
                      _         -> (OutputErr "Wrong parameter")

commandDgGlobSubsume::([ScriptCommandParameters],CmdInterpreterStatus) -> CmdInterpreterStatus
commandDgGlobSubsume (param,status)
     = case status of
        (Env ln libEnv) -> case param of
                              (Goals ls):_ -> let l = getAllGlobalEdgeGoals ln libEnv ls
                                                  result = globSubsumeFromList ln libEnv l
                                              in (Env ln result)
                              _            -> (OutputErr "Wrong parameters")
        _               -> (OutputErr "Wrong parameters")



commandDgAllGlobSubsume::CmdInterpreterStatus -> CmdInterpreterStatus
commandDgAllGlobSubsume arg
                          = case arg of
                               (Env x y) -> let result =(globSubsume x) y in
                                                (Env x result)
                               _         -> (OutputErr "Wrong parameters")

commandDgAllGlobDecomp::CmdInterpreterStatus -> CmdInterpreterStatus
commandDgAllGlobDecomp arg 
                          = case arg of 
                               (Env x y) -> let result= (globDecomp x) y in
                                                (Env x result)
                               _         -> (OutputErr "Wrong parameters")


commandDgGlobDecomp :: ([ScriptCommandParameters],CmdInterpreterStatus) -> CmdInterpreterStatus
commandDgGlobDecomp (param,status) 
       = case status of
          (Env ln libEnv) -> case param of
                               (Goals ls):_ -> let l = getAllGlobalEdgeGoals ln libEnv ls
                                                   result = globDecompFromList ln libEnv l
                                               in (Env ln result)
                               _            -> (OutputErr "Wrong parameters")
          _               -> (OutputErr "Wrong parameters")


commandDgAllLocInfer::CmdInterpreterStatus -> CmdInterpreterStatus                        
commandDgAllLocInfer arg
                        = case arg of
                             (Env x y) -> let result= (localInference x) y in
                                              (Env x result)
                             _         -> (OutputErr "Wrong parameters")


commandDgLocInfer::([ScriptCommandParameters],CmdInterpreterStatus) -> CmdInterpreterStatus
commandDgLocInfer (param,status)
         = case status of 
             (Env ln libEnv) -> case param of
                                  (Goals ls):_ -> let l = getAllLocalEdgeGoals ln libEnv ls
                                                      result = localInferenceFromList ln libEnv l
                                                  in (Env ln result)
                                  _            -> (OutputErr "Wrong parameters")
             _               -> (OutputErr "Wrong parameters")

commandDgAllLocDecomp::CmdInterpreterStatus -> CmdInterpreterStatus
commandDgAllLocDecomp arg
                         = case arg of 
                               (Env x y) -> let result= (locDecomp x) y in
                                                (Env x result)
                               _         -> (OutputErr "Wrong parameters")


commandDgLocDecomp::([ScriptCommandParameters], CmdInterpreterStatus)-> CmdInterpreterStatus
commandDgLocDecomp (param,status)
       = case status of
           (Env ln libEnv) -> case param of
                                (Goals ls):_ -> let l = getAllLocalEdgeGoals ln libEnv ls
                                                    result = locDecompFromList ln libEnv l
                                                in (Env ln result)
                                _            -> (OutputErr "Wrong parameters")
           _               -> (OutputErr "Wrong parameters")


commandDgComp::([ScriptCommandParameters], CmdInterpreterStatus) -> CmdInterpreterStatus
commandDgComp (param, status)
      = case status of
         (Env ln libEnv) -> case param of
                              (Goals ls):_ -> let l = getAllGlobalEdgeGoals ln libEnv ls
                                                  result = compositionFromList ln libEnv l
                                              in (Env ln result)
                              _            -> (OutputErr "Wrong parameters")
         _               -> (OutputErr "Wrong parameters")


commandDgAllComp::CmdInterpreterStatus -> CmdInterpreterStatus
commandDgAllComp arg 
                    = case arg of
                           (Env x y) -> let result= (composition x) y in
                                            (Env x result)
                           _         -> (OutputErr "Wrong parameters")

commandDgCompNew::([ScriptCommandParameters],CmdInterpreterStatus) -> CmdInterpreterStatus
commandDgCompNew (param, status)
        = case status of
           (Env ln libEnv) -> case param of
                                (Goals ls):_ -> let l = getAllGlobalEdgeGoals ln libEnv ls
                                                    result = compositionCreatingEdgesFromList ln libEnv l
                                                in (Env ln result)
                                _            -> (OutputErr "Wrong parameters")
           _               -> (OutputErr "Wrong parameters")

 

commandDgAllCompNew::CmdInterpreterStatus -> CmdInterpreterStatus
commandDgAllCompNew arg
                      = case arg of
                             (Env x y) -> let result=(compositionCreatingEdges x) y in
                                              (Env x result)
                             _         -> (OutputErr "Wrong parameters")

commandDgHideThm::([ScriptCommandParameters],CmdInterpreterStatus) -> CmdInterpreterStatus
commandDgHideThm (param, status)
         = case status of
             (Env ln libEnv) -> case param of
                                  (Goals ls):_  -> let l = getAllHidingThmGoals ln libEnv ls
                                                       result = automaticHideTheoremShiftFromList ln l libEnv
                                                   in (Env ln result)
                                  _             -> (OutputErr "Wrong parameters")
             _               -> (OutputErr "Wrong parameters")

commandDgAllHideThm::CmdInterpreterStatus -> CmdInterpreterStatus
commandDgAllHideThm arg
                      = case arg of
                             (Env x y) -> let result= (automaticHideTheoremShift x) y in
                                              (Env x result)
                             _         -> (OutputErr "Wrong parameters")

commandDgAllThmHide::CmdInterpreterStatus -> CmdInterpreterStatus
commandDgAllThmHide arg
                       = case arg of
                              (Env x y) -> let result=(theoremHideShift x) y in
                                               (Env x result)
                              _         -> (OutputErr "Wrong parameters")

  


-- | The 'findNodeNumber' function, given the Id of a node searches a list of LNode and returns the index of the node
findNodeNumber :: [LNode DGNodeLab] -> Id -> Maybe Node
findNodeNumber ls x 
                   = case ls of
                         []              -> Nothing
                         (nb,label):l    -> if (( getDGNodeName label)==(show x)) then Just nb else findNodeNumber l x 

-- | The 'isEdgeBetween' function checks for two given Node and an edge if the edge is between those nodes
isEdgeBetween:: Node -> Node -> LEdge DGLinkLab -> Bool
isEdgeBetween x y (currentEdgeX,currentEdgeY, currentEdgeLab) =
                                           if ((x==currentEdgeX)&&(y==currentEdgeY)) then True else False 
                               
                   

-- | The 'getAllEdges' function, given the Id of two nodes finds out all edges between those nodes
getAllEdges:: LIB_NAME->LibEnv->Id -> Id -> [LEdge DGLinkLab]
getAllEdges ln libEnv x y =
                    let dgraph     = lookupDGraph ln libEnv
                        xNb   = fromJust $ findNodeNumber (labNodes dgraph) x
                        yNb   = fromJust $ findNodeNumber (labNodes dgraph) y
                    in filter (isEdgeBetween xNb yNb) (labEdges dgraph)
                        

selectLabeledEdge:: Int-> [LEdge DGLinkLab] -> Maybe (LEdge DGLinkLab)
selectLabeledEdge x ls =
                       case x of
                              0 -> case ls of
                                        [] -> Nothing
                                        e:l-> Just e
                              n -> case ls of 
                                        [] -> Nothing
                                        e:l-> selectLabeledEdge (n-1) l


-- | The 'getAllGlobalEdgeGoals' function, given the list of goals extracts only the globalUnprovenThm from all the edges in the list
getAllGlobalEdgeGoals:: LIB_NAME->LibEnv->[GOAL]->[LEdge DGLinkLab]
getAllGlobalEdgeGoals ln libEnv ls =
                     case ls of 
                        []                         -> []
                        (Node _):l                 -> getAllGlobalEdgeGoals ln libEnv l
                        (Edge x y):l               -> let allEdges     = getAllEdges ln libEnv x y
                                                          allGlobalThm = filter isUnprovenGlobalThm allEdges
                                                      in  allGlobalThm ++ (getAllGlobalEdgeGoals ln libEnv l)
                        (LabeledEdge x thelab y):l -> let allEdges     = getAllEdges ln libEnv x y
                                                          allGlobalThm = filter isUnprovenGlobalThm allEdges
                                                          theEdge      = fromJust $ selectLabeledEdge thelab allGlobalThm
                                                      in  theEdge: (getAllGlobalEdgeGoals ln libEnv l)

getAllLocalEdgeGoals:: LIB_NAME->LibEnv->[GOAL]->[LEdge DGLinkLab]
getAllLocalEdgeGoals ln libEnv ls =
                    case ls of                                         
                       []                          -> []
                       (Node _):l                  -> getAllGlobalEdgeGoals ln libEnv l
                       (Edge x y):l                -> let allEdges     = getAllEdges ln libEnv x y
                                                          allLocalThm  = filter isUnprovenLocalThm allEdges
                                                      in  allLocalThm ++ (getAllLocalEdgeGoals ln libEnv l)
                       (LabeledEdge x thelab y):l  -> let allEdges     = getAllEdges ln libEnv x y
                                                          allLocalThm  = filter isUnprovenLocalThm allEdges
                                                          theEdge      = fromJust $ selectLabeledEdge thelab allLocalThm
                                                      in  theEdge : (getAllLocalEdgeGoals ln libEnv l)

getAllHidingThmGoals :: LIB_NAME -> LibEnv -> [GOAL] -> [LEdge DGLinkLab]
getAllHidingThmGoals ln libEnv ls =
                     case ls of 
                       []                          -> []
                       (Node _):l                  -> getAllHidingThmGoals ln libEnv l
                       (Edge x y):l                -> let allEdges     = getAllEdges ln libEnv x y
                                                          allHidingThm = filter isUnprovenHidingThm allEdges
                                                      in  allHidingThm ++ (getAllHidingThmGoals ln libEnv l)
                       (LabeledEdge x thelab y):l  -> let allEdges     = getAllEdges ln libEnv x y
                                                          allHidingThm = filter isUnprovenHidingThm allEdges
                                                          theEdge      = fromJust $ selectLabeledEdge thelab allHidingThm
                                                      in  theEdge : (getAllHidingThmGoals ln libEnv l)

