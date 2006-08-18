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
                      


import Syntax.AS_Library
import Static.DevGraph
import Proofs.EdgeUtils
import Proofs.InferBasic
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
 deriving (Eq,Show)     

data CmdParam =
   Path                          String 
 | Formula                       String 
 | UseProver                     String
 | Goals                         [GOAL]
 | ParsedComorphism             [String]
 | AxiomSelectionWith           [String]
 | AxiomSelectionExcluding      [String]
 | Formulas                     [String]
 | ProofScript                   String
 | ParamErr                      String
 | NoParam
 deriving (Eq,Show)

data Status = 
   OutputErr  String
 | CmdInitialState
 | Env     LIB_NAME LibEnv
 | Selected [GraphGoals]
 | AllGoals [GraphGoals]
 | Comorph [String]
 | Prover String
 | Address String




 
data InterpreterCmd =
   CmdP   ([CmdParam]->IO [Status]) [CmdParam] 
 | CmdPS  (([CmdParam],[Status])-> [Status]) [CmdParam] 
 | CmdS   ([Status] -> [Status])
 | CmdT   ([CmdParam]->IO())  [CmdParam]
 | CmdSS  ([Status] -> IO())
 | CmdSIO ([Status] -> IO [Status]) 
 | CmdE   String
 | EndOfCommands


extractGraphNode:: String->[GraphGoals]->Maybe GraphGoals
extractGraphNode x allGoals 
    = case allGoals of
       []              -> Nothing
       (GraphNode (nb,label)):l    -> if (( getDGNodeName label)==x) 
                                          then Just (GraphNode (nb,label))
                                          else extractGraphNode x l
       _:l                           -> extractGraphNode x l
         

extractGraphEdge:: String -> String -> [GraphGoals] -> Maybe GraphGoals
extractGraphEdge x y allGoals
   = case allGoals of
      []             -> Nothing
      (GraphEdge (xx,yy,label)):l -> 
                  let t1 = fromJust $ extractGraphNode x allGoals
                      t2 = fromJust $ extractGraphNode y allGoals
                  in case t1 of 
                    (GraphNode (tmp1_nb, _)) ->
                       case t2 of
                        (GraphNode (tmp2_nb, _)) ->
                          if (tmp1_nb == xx) 
                            then if (tmp2_nb == yy) 
                               then Just (GraphEdge (xx,yy,label))
                               else extractGraphEdge x y l
                            else extractGraphEdge x y l
                        _ -> extractGraphEdge x y l
                    _ -> extractGraphEdge x y l  
      _:l    -> extractGraphEdge x y l                                                             

extractGraphLabeledEdge:: String -> Int -> String -> 
                          [GraphGoals] -> Maybe GraphGoals
extractGraphLabeledEdge x nb y allGoals
    = case allGoals of
      []             -> Nothing
      (GraphEdge (xx,yy,label)):l  -> 
                  let t1 = fromJust $ extractGraphNode x allGoals
                      t2 = fromJust $ extractGraphNode y allGoals
                  in case t1 of 
                    (GraphNode (tmp1_nb, _)) ->
                       case t2 of
                        (GraphNode (tmp2_nb, _)) ->
                          if (tmp1_nb == xx) 
                            then if (tmp2_nb == yy) 
                               then if (nb==0)  
                                 then Just (GraphEdge (xx,yy,label))
                                 else extractGraphLabeledEdge x (nb-1) y l
                               else extractGraphLabeledEdge x nb y l
                            else extractGraphLabeledEdge x nb y l
                        _ -> extractGraphLabeledEdge x nb y l
                    _ -> extractGraphLabeledEdge x nb y l  
      _:l -> extractGraphLabeledEdge x nb y l 



getGoalList :: [GOAL] -> [GraphGoals] -> [GraphGoals]
getGoalList goalList allg 
 = case goalList of
    (Node x):l -> 
      (fromJust $ extractGraphNode x allg):(getGoalList l allg)
    (Edge x y):l ->
      (fromJust $ extractGraphEdge x y allg):(getGoalList l allg)
    (LabeledEdge x nb y):l ->
      (fromJust $ extractGraphLabeledEdge x nb y allg):(getGoalList l allg)
    [] -> 
       []

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
               (nb,x):l  -> if (hasOpenGoals x) 
                              then (GraphNode (nb,x)):(getNodeGoals l)
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


update::[Status] -> [Status] -> [Status]
update val status
 = case val of
    []                  ->  status
    (Env x y):l         -> 
      case status of
       []                 -> update l [Env x y]
       CmdInitialState:ls -> update ((Env x y):l) ls
       (OutputErr xx):_   -> (OutputErr xx):[]
       (Env _ _):ls       -> update l ((Env x y):ls)
       (Selected xx):ls   -> update l ((Selected xx):(update [Env x y] ls))
       (AllGoals xx):ls   -> update l ((AllGoals xx):(update [Env x y] ls))
       (Comorph xx):ls    -> update l ((Comorph xx):(update [Env x y] ls))
       (Prover xx):ls     -> update l ((Prover xx):(update [Env x y] ls))
       (Address xx):ls    -> update l ((Address xx):(update [Env x y] ls))
    (Selected x):l -> 
      case status of
       []                 -> update l [Selected x]
       CmdInitialState:ls -> update ((Selected x):l) ls
       (OutputErr xx):_   -> (OutputErr xx):[]
       (Env xx yy):ls     -> update l ((Env xx yy):(update [Selected x] ls))
       (Selected _):ls    -> update l ((Selected x):ls)
       (AllGoals xx):ls   -> update l ((AllGoals xx):(update [Selected x] ls))
       (Comorph xx):ls    -> update l ((Comorph xx):(update [Selected x] ls))
       (Prover xx):ls     -> update l ((Prover xx):(update [Selected x] ls))
       (Address xx):ls    -> update l ((Address xx):(update [Selected x] ls))
    (AllGoals x):l -> 
      case status of
       []                 -> update  l [AllGoals x] 
       CmdInitialState:ls -> update  ((AllGoals x):l) ls 
       (OutputErr xx):_   -> (OutputErr xx):[]
       (Env xx yy):ls     -> update l ((Env xx yy):(update [AllGoals x] ls))
       (Selected xx):ls   -> update l ((Selected xx):(update [AllGoals x] ls))
       (AllGoals _):ls    -> update l ((AllGoals x):ls)
       (Comorph xx):ls    -> update l ((Comorph xx):(update [AllGoals x] ls))
       (Prover xx):ls     -> update l ((Prover xx): (update [AllGoals x] ls))
       (Address xx):ls    -> update l ((Address xx):(update [AllGoals x] ls))
    (Comorph x):l -> 
      case status of
       []                 -> update l [Comorph x]
       CmdInitialState:ls -> update ((Comorph x):l) ls
       (OutputErr xx):_   -> (OutputErr xx):[]
       (Env xx yy):ls     -> update l ((Env xx yy):(update [Comorph x] ls))
       (Selected xx):ls   -> update l ((Selected xx):(update [Comorph x] ls))
       (AllGoals xx):ls   -> update l ((AllGoals xx):(update [Comorph x] ls))
       (Comorph _):ls     -> update l ((Comorph x):ls)
       (Prover xx):ls     -> update l ((Prover xx):(update  [Comorph x] ls))
       (Address xx):ls    -> update l ((Address xx):(update [Comorph x] ls))
    (Prover x):l    -> 
      case status of
       []                 -> update l [Prover x]
       CmdInitialState:ls -> update ((Prover x):l) ls
       (OutputErr xx):_   -> (OutputErr xx):[]
       (Env xx yy):ls     -> update l ((Env xx yy):(update [Prover x] ls))
       (Selected xx):ls   -> update l ((Selected xx):(update [Prover x] ls))
       (AllGoals xx):ls   -> update l ((AllGoals xx):(update [Prover x] ls))
       (Comorph xx):ls    -> update l ((Comorph xx):(update [Prover x] ls))
       (Prover _):ls      -> update l ((Prover x):ls)
       (Address xx):ls    -> update l ((Address xx):(update [Prover x] ls))
    (Address x):l   ->
      case status of
       []                 -> update l [Address x]
       CmdInitialState:ls -> update ((Address x):l) ls
       (OutputErr xx):_   -> (OutputErr xx):[]
       (Env xx yy):ls     -> update l ((Env xx yy):(update [Address x] ls))
       (Selected xx):ls   -> update l ((Selected xx):(update [Address x] ls))
       (AllGoals xx):ls   -> update l ((AllGoals xx):(update [Address x] ls))
       (Comorph xx):ls    -> update l ((Comorph xx):(update [Address x] ls))
       (Prover xx):ls     -> update l ((Prover xx):(update [Address x] ls))
       (Address _):ls     -> update l ((Address x):ls)
    (OutputErr x):_       -> (OutputErr x):[]
    CmdInitialState:l     -> update l status




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
   GraphNode (_,(DGNode _ theTh _ _ _ _ _)) -> 
                    putStr  ((showDoc theTh "\n") ++ "\n")
   _      -> putStr "Not a node!\n" 


printNodeInfoFromList :: [GraphGoals] -> IO()
printNodeInfoFromList ls =
              case ls of
                     (GraphNode (x1,(DGNode x2 x3 x4 x5 x6 x7 x8))):l -> do
                                          printNodeInfo (GraphNode (x1,(DGNode x2 x3 x4 x5 x6 x7 x8)))
                                          result <-printNodeInfoFromList l
                                          return result
                     _:l             -> do 
                                         result<- printNodeInfoFromList l
                                         return result
                     []              -> return ()

printNodeInfo :: GraphGoals -> IO()
printNodeInfo x =
       case x of
          GraphNode (_, (DGNode tname _ _ _ _ _ _)) -> 
                                        putStr (( showName tname)++"\n")
          _                          -> putStr "Not a node!\n"


printNodeTaxonomyFromList :: TaxoGraphKind -> [GraphGoals]-> IO()
printNodeTaxonomyFromList kind ls =
             case ls of
                   (GraphNode x):l -> 
                       do 
                          printNodeTaxonomy kind (GraphNode x)
                          result <- printNodeTaxonomyFromList kind l
                          return result
                   _:l -> 
                       do
                          result <- printNodeTaxonomyFromList kind l
                          return result
                   []  -> return ()


printNodeTaxonomy :: TaxoGraphKind -> GraphGoals -> IO()
printNodeTaxonomy kind x =
   case x of 
     GraphNode (_, (DGNode tname thTh _ _ _ _ _)) -> 
                           displayGraph kind (show tname) thTh
     _            -> putStr "Not a node!\n"
        

proveNodes :: [GraphGoals] -> LIB_NAME ->LibEnv -> IO LibEnv
proveNodes ls ln libEnv
     = case ls of
        (GraphNode (nb, _)):l -> 
           do
             result <- basicInferenceNode False logicGraph (ln,nb) ln libEnv
             case result of 
                  Result _ (Just nwEnv)  -> proveNodes l ln nwEnv
                  _                      -> proveNodes l ln libEnv
        _:l                   -> proveNodes l ln libEnv
        []                    -> return libEnv

