{- |
Module      :$Header$
Copyright   : uni-bremen and Razvan Pascanu
Licence     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@iu-bremen.de
Stability   : provisional
Portability : portable

Usefull function used by the parser.


   TODO 
       - add comment.

-} 

module PGIP.Common where
                      


import Proofs.EdgeUtils
import Data.Graph.Inductive.Graph
import Syntax.AS_Library
import Static.AnalysisLibrary
import Static.DevGraph
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

type GDataEdge = LEdge DGLinkLab
type GDataNode = LNode DGNodeLab

data GOAL = 
   Node         String   
 | Edge         String   String     
 | LabeledEdge  String   Int     String 
 deriving (Eq,Show)

data GraphGoals =
   GraphNode  GDataNode
 | GraphEdge  GDataEdge
-- | GraphGlobalEdge [GDataEdge]
-- | GraphHidingEdge [GDataEdge]
 deriving (Eq,Show)     

data ScriptCommandParameters =
   Path                         [String] 
 | Formula                       String 
 | Prover                        String
 | Goals                         [GOAL]
 | ParsedComorphism             [String]
 | AxiomSelectionWith           [String]
 | AxiomSelectionExcluding      [String]
 | Formulas                     [String]
 | ProofScript                   String
 | ParamErr                      String
 | NoParam
 deriving (Eq,Show)

data CmdInterpreterStatus = 
   OutputErr  String
 | CmdInitialState
 | Env     LIB_NAME LibEnv
 | Selected [GraphGoals]
 | AllGraphGoals [GraphGoals]
 | Comorphism [String]
 | ProverUsed String




 
data CommandFunctionsAndParameters=
   CommandParam        ([ScriptCommandParameters]->IO [CmdInterpreterStatus]) [ScriptCommandParameters] 
 | CommandParamStatus  (([ScriptCommandParameters],[CmdInterpreterStatus])-> [CmdInterpreterStatus]) [ScriptCommandParameters] 
 | CommandStatus       ([CmdInterpreterStatus] -> [CmdInterpreterStatus])
 | CommandTest         ([ScriptCommandParameters]->IO())  [ScriptCommandParameters]
 | CommandShowStatus   ([CmdInterpreterStatus] -> IO())
 | CommandStatusIO     ([CmdInterpreterStatus] -> IO [CmdInterpreterStatus]) 
 | CommandError        String


extractGraphNode:: String->[GraphGoals]->Maybe GraphGoals
extractGraphNode x allGoals 
    = case allGoals of
       []              -> Nothing
       (GraphNode (nb,label)):l    -> if (( getDGNodeName label)==x) then Just (GraphNode (nb,label)) 
                                                                            else extractGraphNode x l
       _:l                           -> extractGraphNode x l
         

extractGraphEdge:: String -> String -> [GraphGoals] -> Maybe GraphGoals
extractGraphEdge x y allGoals
   = case allGoals of
      []             -> Nothing
      (GraphEdge (xx,yy,label)):l  -> let tmp1 = fromJust $ extractGraphNode x allGoals
                                          tmp2 = fromJust $ extractGraphNode y allGoals
                                      in case tmp1 of 
                                           (GraphNode (tmp1_nb, tmp1_lab)) ->
                                                case tmp2 of
                                                   (GraphNode (tmp2_nb, tmp2_lab)) ->
                                                          if (tmp1_nb == xx) 
                                                              then if (tmp2_nb == yy) then Just (GraphEdge (xx,yy,label))
                                                                                      else extractGraphEdge x y l
                                                              else extractGraphEdge x y l
                                                   _ -> extractGraphEdge x y l
                                           _ -> extractGraphEdge x y l  
                                                               

extractGraphLabeledEdge:: String -> Int -> String -> [GraphGoals] -> Maybe GraphGoals
extractGraphLabeledEdge x nb y allGoals
    = case allGoals of
      []             -> Nothing
      (GraphEdge (xx,yy,label)):l  -> let tmp1 = fromJust $ extractGraphNode x allGoals
                                          tmp2 = fromJust $ extractGraphNode y allGoals
                                      in case tmp1 of 
                                           (GraphNode (tmp1_nb, tmp1_lab)) ->
                                                case tmp2 of
                                                   (GraphNode (tmp2_nb, tmp2_lab)) ->
                                                          if (tmp1_nb == xx) 
                                                              then if (tmp2_nb == yy) 
                                                                  then if (nb==0)  
                                                                       then Just (GraphEdge (xx,yy,label))
                                                                       else extractGraphLabeledEdge x (nb-1) y l
                                                                  else extractGraphLabeledEdge x nb y l
                                                              else extractGraphLabeledEdge x nb y l
                                                   _ -> extractGraphLabeledEdge x nb y l
                                           _ -> extractGraphLabeledEdge x nb y l  
  



getGoalList :: [GOAL] -> [GraphGoals] -> [GraphGoals]
getGoalList goalList allGoals 
                    = case goalList of
                          (Node x):l             -> (fromJust $ extractGraphNode x allGoals):(getGoalList l allGoals)
                          (Edge x y):l           -> (fromJust $ extractGraphEdge x y allGoals):(getGoalList l allGoals)
                          (LabeledEdge x nb y):l ->(fromJust $ extractGraphLabeledEdge x nb y allGoals):(getGoalList l allGoals)
                          []                     -> []

getEdgeGoals::[GDataEdge] -> [GraphGoals] 
getEdgeGoals ls =
          case ls of 
               x:l   -> if (isUnprovenGlobalThm x) 
                         then (GraphEdge x):(getEdgeGoals l)
                         else if (isUnprovenLocalThm x) 
                           then (GraphEdge x):(getEdgeGoals l)
                           else if (isUnprovenHidingThm x) 
                               then (GraphEdge x):(getEdgeGoals l)
                               else getEdgeGoals l
               []    -> []

getNodeGoals::[GDataNode] -> [GraphGoals]
getNodeGoals ls =
         case ls of
               (nb,x):l  -> if (hasOpenGoals x) then (GraphNode (nb,x)):(getNodeGoals l)
                                           else getNodeGoals l
               []   -> []

createAllGoalsList :: LIB_NAME->LibEnv -> [GraphGoals]
createAllGoalsList ln libEnv
                    = let dgraph = lookupDGraph ln libEnv
                          edgeGoals = getEdgeGoals (labEdges dgraph)
                          nodeGoals = getNodeGoals (labNodes dgraph)
                      in edgeGoals ++ nodeGoals


getEdgeList :: [GraphGoals] -> [GDataEdge]
getEdgeList ls =
        case ls of 
             (GraphEdge x):l  -> x:(getEdgeList l)
             (GraphNode _):l  -> getEdgeList l
             []               -> []

getNodeList :: [GraphGoals] -> [GDataNode]
getNodeList ls =
       case ls of 
            (GraphEdge _):l  -> getNodeList l
            (GraphNode x):l  -> x:(getNodeList l)
            []               -> []


addOrReplace::([CmdInterpreterStatus],[CmdInterpreterStatus])->[CmdInterpreterStatus]
addOrReplace (val,status)
   = case val of
      []                  ->  status
      (Env x y):l         -> case status of
                              []                    -> addOrReplace(l,(Env x y):[])
                              CmdInitialState:ls    -> addOrReplace ((Env x y):l,ls)
                              (OutputErr xx):_      -> (OutputErr xx):[]
                              (Env _ _):ls          -> addOrReplace(l,(Env x y):ls)
                              (Selected xx):ls      -> addOrReplace(l, (Selected xx):addOrReplace([Env x y],ls))
                              (AllGraphGoals xx):ls -> addOrReplace(l, (AllGraphGoals xx):addOrReplace([Env x y],ls))
                              (Comorphism xx):ls    -> addOrReplace(l, (Comorphism xx):addOrReplace([Env x y],ls))
                              (ProverUsed xx):ls    -> addOrReplace(l, (ProverUsed xx):addOrReplace([Env x y],ls))
      (Selected x):l -> case status of
                              []                    -> addOrReplace (l,(Selected x):[])
                              CmdInitialState:ls    -> addOrReplace ((Selected x):l, ls)
                              (OutputErr xx):_      -> (OutputErr xx):[]
                              (Env xx yy):ls        -> addOrReplace(l, (Env xx yy):addOrReplace([Selected x], ls))
                              (Selected _):ls       -> addOrReplace(l, (Selected x):ls)
                              (AllGraphGoals xx):ls -> addOrReplace(l, (AllGraphGoals xx):addOrReplace([Selected x],ls))
                              (Comorphism xx):ls    -> addOrReplace(l, (Comorphism xx):addOrReplace([Selected x],ls))
                              (ProverUsed xx):ls    -> addOrReplace(l, (ProverUsed xx):addOrReplace([Selected x],ls))
      (AllGraphGoals x):l -> case status of
                              []                    -> addOrReplace (l,(AllGraphGoals x):[])
                              CmdInitialState:ls    -> addOrReplace ((AllGraphGoals x):l,ls)
                              (OutputErr xx):_      -> (OutputErr xx):[]
                              (Env xx yy):ls        -> addOrReplace(l, (Env xx yy):addOrReplace([AllGraphGoals x], ls))
                              (Selected xx):ls      -> addOrReplace(l, (Selected xx):addOrReplace([AllGraphGoals x], ls))
                              (AllGraphGoals _):ls  -> addOrReplace(l, (AllGraphGoals x):ls)
                              (Comorphism xx):ls    -> addOrReplace(l, (Comorphism xx):addOrReplace([AllGraphGoals x], ls))
                              (ProverUsed xx):ls    -> addOrReplace(l, (ProverUsed xx):addOrReplace([AllGraphGoals x], ls))
      (Comorphism x):l    -> case status of
                              []                    -> addOrReplace (l, (Comorphism x):[])
                              CmdInitialState:ls    -> addOrReplace ((Comorphism x):l, ls)
                              (OutputErr xx):_      -> (OutputErr xx):[]
                              (Env xx yy):ls        -> addOrReplace (l, (Env xx yy):addOrReplace([Comorphism x], ls))
                              (Selected xx):ls      -> addOrReplace (l, (Selected xx):addOrReplace([Comorphism x],ls))
                              (AllGraphGoals xx):ls -> addOrReplace (l, (AllGraphGoals xx):addOrReplace([Comorphism x],ls))
                              (Comorphism _):ls     -> addOrReplace (l, (Comorphism x):ls)
                              (ProverUsed xx):ls    -> addOrReplace (l, (ProverUsed xx):addOrReplace([Comorphism x],ls))
      (ProverUsed x):l    -> case status of
                              []                    -> addOrReplace (l, (ProverUsed x):[])
                              CmdInitialState:ls    -> addOrReplace ((ProverUsed x):l, ls)
                              (OutputErr xx):_      -> (OutputErr xx):[]
                              (Env xx yy):ls        -> addOrReplace (l, (Env xx yy):addOrReplace([ProverUsed x], ls))
                              (Selected xx):ls      -> addOrReplace (l, (Selected xx):addOrReplace([ProverUsed x], ls))
                              (AllGraphGoals xx):ls -> addOrReplace (l, (AllGraphGoals xx):addOrReplace([ProverUsed x], ls))
                              (Comorphism xx):ls    -> addOrReplace (l, (Comorphism xx):addOrReplace([ProverUsed x], ls))
                              (ProverUsed _):ls     -> addOrReplace (l, (ProverUsed x):ls)
      (OutputErr x):l     -> (OutputErr x):[]
      CmdInitialState:l   -> addOrReplace (l,status)



printNodeTheoryFromList :: [GraphGoals]-> IO()
printNodeTheoryFromList ls =
                case ls of 
                     (GraphNode x):l -> do 
                                         printNodeTheory (GraphNode x)
                                         result<- printNodeTheoryFromList l
                                         return result
                     _:l   -> do
                                result <-printNodeTheoryFromList l
                                return result
                     []    -> return ()

printNodeTheory :: GraphGoals -> IO()
printNodeTheory arg =
                 case arg of
                       GraphNode (_,(DGNode _ theTh _ _ _ _ _)) -> putStr  ((showDoc theTh "\n") ++ "\n")
                       _                                        -> putStr "Not a node!\n" 


printNodeInfoFromList :: [GraphGoals] -> IO()
printNodeInfoFromList ls =
              case ls of
                     (GraphNode x):l -> do
                                          printNodeInfo (GraphNode x)
                                          result <-printNodeInfoFromList l
                                          return result
                     _:l             -> do 
                                         result<- printNodeInfoFromList l
                                         return result
                     []              -> return ()

printNodeInfo :: GraphGoals -> IO()
printNodeInfo x =
              case x of
                    GraphNode (_, (DGNode tname _ _ _ _ _ _)) -> putStr (( showName tname)++"\n")
                    _                                       -> putStr "Not a node!\n"


printNodeTaxonomyFromList :: TaxoGraphKind -> [GraphGoals]-> IO()
printNodeTaxonomyFromList kind ls =
             case ls of
                   (GraphNode x):l -> do 
                                        printNodeTaxonomy kind (GraphNode x)
                                        result <- printNodeTaxonomyFromList kind l
                                        return result
                   _:l             -> do
                                       result <- printNodeTaxonomyFromList kind l
                                       return result
                   []              -> return ()


printNodeTaxonomy :: TaxoGraphKind -> GraphGoals -> IO()
printNodeTaxonomy kind x =
              case x of 
                   GraphNode (_, (DGNode tname thTh _ _ _ _ _)) -> displayGraph kind (show tname) thTh
                   _                                            -> putStr "Not a node!\n"
        

proveNodes :: [GraphGoals] -> LIB_NAME ->LibEnv -> IO LibEnv
proveNodes ls ln libEnv
     = case ls of
             (GraphNode (nb, _)):l -> do
                                        result <- basicInferenceNode False logicGraph (ln,nb) ln libEnv
                                        case result of 
                                            Result _ (Just nwEnv)  -> proveNodes l ln nwEnv
                                            _                        -> proveNodes l ln libEnv
             _:l                   -> proveNodes l ln libEnv
             []                    -> return libEnv

