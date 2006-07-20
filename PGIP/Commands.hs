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
import Data.Maybe
import Data.Graph.Inductive.Graph
import Comorphisms.LogicGraph

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
 | SelectedNodes [Node]


data CmdInterpreterStatusID =
   EnvID
 
data CommandFunctionsAndParameters=
   CommandParam        ([ScriptCommandParameters]->IO [CmdInterpreterStatus]) [ScriptCommandParameters] 
 | CommandParamStatus  (([ScriptCommandParameters],[CmdInterpreterStatus])-> [CmdInterpreterStatus]) [ScriptCommandParameters] [CmdInterpreterStatusID]
 | CommandStatus       ([CmdInterpreterStatus] -> [CmdInterpreterStatus]) [CmdInterpreterStatusID]
 | CommandTest         ([ScriptCommandParameters]->IO())  [ScriptCommandParameters]
 | CommandShowStatus   ([CmdInterpreterStatus] -> ()) [CmdInterpreterStatusID]
 | CommandError



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
                                      Just (name,env) ->  return [(Env name env)] 
                                      Nothing ->  return [(OutputErr "Couldn't load the file specified")]
                _             -> return [(OutputErr "Wrong parameter")]

commandDgAllAuto::[CmdInterpreterStatus] -> [CmdInterpreterStatus]
commandDgAllAuto arg
                 = case arg of
                      (Env x y):_   -> let result= automatic x y 
                                       in  [(Env x result)]
                      _:l           -> commandDgAllAuto l
                      []            -> [(OutputErr "Wrong parameter")]

commandDgAuto :: ([ScriptCommandParameters],[CmdInterpreterStatus]) -> [CmdInterpreterStatus]
commandDgAuto (param,status)
       = case status of
           (Env ln libEnv):_ -> case param of
                                   (Goals ls):_ -> let l = getAllEdgeGoals ln libEnv ls
                                                       result = automaticFromList ln l libEnv
                                                       in [(Env ln result)]
                                   _            -> [(OutputErr "Wrong parameters")]
           _:l               -> commandDgAuto (param, l)
           []                -> [(OutputErr "Wrong parameters")]

commandDgGlobSubsume::([ScriptCommandParameters],[CmdInterpreterStatus]) -> [CmdInterpreterStatus]
commandDgGlobSubsume (param,status)
     = case status of
        (Env ln libEnv):_  -> case param of
                               (Goals ls):_ -> let l = getAllGlobalEdgeGoals ln libEnv ls
                                                   result = globSubsumeFromList ln l libEnv 
                                               in [(Env ln result)]
                               _            -> [(OutputErr "Wrong parameters")]
        _:l                -> commandDgGlobSubsume (param,l)
        []                 -> [(OutputErr "Wrong parameters")]



commandDgAllGlobSubsume::[CmdInterpreterStatus] -> [CmdInterpreterStatus]
commandDgAllGlobSubsume arg
                          = case arg of
                               (Env x y):_  -> let result =(globSubsume x) y 
                                               in  [(Env x result)]
                               _:l          -> commandDgAllGlobSubsume l
                               []           -> [(OutputErr "Wrong parameters")]

commandDgAllGlobDecomp::[CmdInterpreterStatus] -> [CmdInterpreterStatus]
commandDgAllGlobDecomp arg 
                          = case arg of 
                               (Env x y):_ -> let result= (globDecomp x) y 
                                              in  [(Env x result)]
                               _:l         -> commandDgAllGlobDecomp l
                               []          -> [(OutputErr "Wrong parameters")]


commandDgGlobDecomp :: ([ScriptCommandParameters],[CmdInterpreterStatus]) -> [CmdInterpreterStatus]
commandDgGlobDecomp (param,status) 
       = case status of
          (Env ln libEnv):_ -> case param of
                                (Goals ls):_ -> let l = getAllGlobalEdgeGoals ln libEnv ls
                                                    result = globDecompFromList ln l libEnv 
                                                in [(Env ln result)]
                                _            -> [(OutputErr "Wrong parameters")]
          _:l               -> commandDgGlobDecomp (param,l)
          []                -> [(OutputErr "Wrong parameters")]


commandDgAllLocInfer::[CmdInterpreterStatus] -> [CmdInterpreterStatus]                        
commandDgAllLocInfer arg
                        = case arg of
                             (Env x y):_ -> let result= (localInference x) y 
                                            in  [(Env x result)]
                             _:l         -> commandDgAllLocInfer l
                             []          -> [(OutputErr "Wrong parameters")]


commandDgLocInfer::([ScriptCommandParameters],[CmdInterpreterStatus]) -> [CmdInterpreterStatus]
commandDgLocInfer (param,status)
         = case status of 
             (Env ln libEnv):_ -> case param of
                                  (Goals ls):_ -> let l = getAllLocalEdgeGoals ln libEnv ls
                                                      result = localInferenceFromList ln l libEnv 
                                                  in [(Env ln result)]
                                  _            -> [(OutputErr "Wrong parameters")]
             _:l               -> commandDgLocInfer (param,l)
             []                -> [(OutputErr "Wrong parameters")]

commandDgAllLocDecomp::[CmdInterpreterStatus] -> [CmdInterpreterStatus]
commandDgAllLocDecomp arg
                         = case arg of 
                               (Env x y):l -> let result= (locDecomp x) y 
                                              in  [(Env x result)]
                               _:l         -> commandDgAllLocDecomp l
                               []          -> [(OutputErr "Wrong parameters")]


commandDgLocDecomp::([ScriptCommandParameters], [CmdInterpreterStatus])-> [CmdInterpreterStatus]
commandDgLocDecomp (param,status)
       = case status of
           (Env ln libEnv):_ -> case param of
                                 (Goals ls):_ -> let l = getAllLocalEdgeGoals ln libEnv ls
                                                     result = locDecompFromList ln l libEnv 
                                                 in  [(Env ln result)]
                                 _            -> [(OutputErr "Wrong parameters")]
           _:l               -> commandDgLocDecomp (param,l)
           []                -> [(OutputErr "Wrong parameters")]


commandDgComp::([ScriptCommandParameters], [CmdInterpreterStatus]) -> [CmdInterpreterStatus]
commandDgComp (param, status)
      = case status of
         (Env ln libEnv):_ -> case param of
                               (Goals ls):_ -> let l = getAllGlobalEdgeGoals ln libEnv ls
                                                   result = compositionFromList ln l libEnv 
                                               in [(Env ln result)]
                               _            -> [(OutputErr "Wrong parameters")]
         _:l               -> commandDgComp (param, l)
         []                -> [(OutputErr "Wrong parameters")]


commandDgAllComp::[CmdInterpreterStatus] -> [CmdInterpreterStatus]
commandDgAllComp arg 
                    = case arg of
                           (Env x y):_ -> let result= (composition x) y 
                                          in  [(Env x result)]
                           _:l         -> commandDgAllComp l
                           []          -> [(OutputErr "Wrong parameters")]

commandDgCompNew::([ScriptCommandParameters],[CmdInterpreterStatus]) -> [CmdInterpreterStatus]
commandDgCompNew (param, status)
        = case status of
           (Env ln libEnv):_ -> case param of
                                  (Goals ls):_ -> let l = getAllGlobalEdgeGoals ln libEnv ls
                                                      result = compositionCreatingEdgesFromList ln l libEnv 
                                                  in [(Env ln result)]
                                  _            -> [(OutputErr "Wrong parameters")]
           _:l               -> commandDgCompNew (param,l)
           []                -> [(OutputErr "Wrong parameters")]

 

commandDgAllCompNew::[CmdInterpreterStatus] -> [CmdInterpreterStatus]
commandDgAllCompNew arg
                      = case arg of
                             (Env x y):_ -> let result=(compositionCreatingEdges x) y 
                                            in  [(Env x result)]
                             _:l         -> commandDgAllCompNew l
                             []          -> [(OutputErr "Wrong parameters")]

commandDgHideThm::([ScriptCommandParameters],[CmdInterpreterStatus]) -> [CmdInterpreterStatus]
commandDgHideThm (param, status)
         = case status of
             (Env ln libEnv):_ -> case param of
                                    (Goals ls):_  -> let l = getAllHidingThmGoals ln libEnv ls
                                                         result = automaticHideTheoremShiftFromList ln l libEnv
                                                     in [(Env ln result)]
                                    _             -> [(OutputErr "Wrong parameters")]
             _:l               -> commandDgHideThm (param,l)
             []                -> [(OutputErr "Wrong parameters")]

commandDgAllHideThm::[CmdInterpreterStatus] -> [CmdInterpreterStatus]
commandDgAllHideThm arg
                      = case arg of
                             (Env x y):_ -> let result= (automaticHideTheoremShift x) y 
                                            in  [(Env x result)]
                             _:l         -> commandDgAllHideThm l
                             []          -> [(OutputErr "Wrong parameters")]

commandDgAllThmHide::[CmdInterpreterStatus] -> [CmdInterpreterStatus]
commandDgAllThmHide arg
                       = case arg of
                              (Env x y):_ -> let result=(theoremHideShift x) y 
                                             in  [(Env x result)]
                              _:l         -> commandDgAllThmHide l
                              []          -> [(OutputErr "Wrong parameters")]


commandDgAllInferBasic::[CmdInterpreterStatus] -> [CmdInterpreterStatus]
commandDgAllInferBasic arg
                        = case arg of
                               (Env x y):_ -> let dgraph = lookupDGraph x y
                                                  lno    = labNodes dgraph
                                                  ls     = extractDGNodeLab lno
                                                  ll     = filter hasOpenGoals ls
--                                                  result = applyInferBasic ll x y
                                              in (Env x y):(SelectedNodes (extractNode lno)):[]
                               _:l         -> commandDgAllInferBasic l
                               []          -> [(OutputErr "Wrong parameters")]



extractDGNodeLab :: [LNode DGNodeLab] -> [DGNodeLab]
extractDGNodeLab ls =
                     case ls of
                        []            -> []
                        (_,r):l       -> r:(extractDGNodeLab l)

extractNode :: [LNode DGNodeLab] -> [Node]
extractNode ls =
                  case ls of 
                     []            -> []
                     (r,_):l       -> r:(extractNode l)

commandShowTheory :: [CmdInterpreterStatus] -> ()
commandShowTheory arg
       = case arg of
           (Env x y):l  -> case l of
                             (SelectedNodes ll):_  -> let dgraph = lookupDGraph x y
                                                      in  printAllTheory ll dgraph
                             _:ls                  -> commandShowTheory ((Env x y):ls)
                             []                    -> ()
           (SelectedNodes ll):l -> case l of
                                    (Env  x y):_ ->  let dgraph = lookupDGraph x y
                                                     in  printAllTheory ll dgraph
                                    _:ls         -> commandShowTheory ((SelectedNodes ll):ls)
                                    []           -> ()



printAllTheory::   [Node] ->DGraph -> ()
printAllTheory ls dgraph
          = case ls of 
                  x:l -> 
                            let dgnode = lab' (context dgraph x)
                                theTh = fromJust $ getNodeByNumber (labNodes dgraph) x
                                str = showDoc theTh "\n"
--                            let thName = showName (dgn_name x)
--                          putStr ( "\n\n"++str++"\n")
                            in printAllTheory l dgraph
                  []  ->  ()

getNodeByNumber :: [LNode DGNodeLab] -> Node -> Maybe G_theory 
getNodeByNumber ls x = case ls of
                        (xx,(DGNode _ theTh _ _ _ _ _)):l -> if (x==xx) then (Just theTh)
                                                                        else getNodeByNumber l x
                        _:l                               -> getNodeByNumber l x 
                        []                                -> Nothing


commandDgInferBasic::([ScriptCommandParameters],[CmdInterpreterStatus]) -> [CmdInterpreterStatus]
commandDgInferBasic (param, status)
      = case status of
          (Env ln libEnv):_ -> case param of
                                 (Goals ls):_ -> let dgraph = lookupDGraph ln libEnv
                                                     lno    = labNodes dgraph 
                                                     ll = getAllNodeGoals lno ls
--                                                     result = applyInferBasic ll ln libEnv
                                                 in  (Env ln libEnv):(SelectedNodes ll):[] 
                                 _            -> [(OutputErr "Wrong parameters")]
          _:l               -> commandDgInferBasic (param, l)
          []                -> [(OutputErr "Wrong parameters")]
                                        

--applyInferBasic:: [Node] -> LIB_NAME -> LibEnv -> LibEnv
--applyInferBasic ll ln libEnv
--      = case ll of
--             x:l         -> do 
--                            (Result _ r) <- basicInferenceNode False logicGraph (ln,x) ln libEnv
--                            applyInferBasic l ln  (fromJust r)
--             []          -> libEnv
            

getAllNodeGoals :: [LNode DGNodeLab]->[GOAL] -> [Node]
getAllNodeGoals lno ls
       = case ls of
             (Edge _ _):l          -> getAllNodeGoals lno l
             (LabeledEdge _ _ _):l -> getAllNodeGoals lno l
             (Node x):l            -> (fromJust $ findNodeNumber lno x):(getAllNodeGoals  lno l)
             []                    -> []



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
                        lno        = labNodes dgraph
                        xNb   = fromJust $ findNodeNumber lno x
                        yNb   = fromJust $ findNodeNumber lno y
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


getAllEdgeGoals :: LIB_NAME->LibEnv ->[GOAL]->[LEdge DGLinkLab]
getAllEdgeGoals ln libEnv ls =
                                (getAllGlobalEdgeGoals ln libEnv ls)++(getAllLocalEdgeGoals ln libEnv ls);

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



                             
