{- |
Module      :$Header$
Description : utilities for Hets commands
Copyright   : uni-bremen and Razvan Pascanu
Licence     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@iu-bremen.de
Stability   : provisional
Portability : portable

Together with "PGIP.Common", "PGIP.Utils" contains all the auxiliary functions
used throughout the interactive interface. The reason for dividing these
functions in two files was that otherwise we would had circular 
imports (for example "Proofs.Automatic" requires some of these auxiliary 
functions, but some other functions -- that appear now in "PGIP.Common" -- 
require some functions from "Proofs.Automatic")
-} 

{- todo: refactor getGoalList, extractGraphEdge, extractGraphLabeledEdge
to pure functions with less duplicate code! -}

module PGIP.Utils where
import Data.Graph.Inductive.Graph
import Static.DevGraph
import Syntax.AS_Library
import Data.List (find)

type GDataEdge = LEdge DGLinkLab
type GDataNode = LNode DGNodeLab

data GraphGoals =
   GraphNode GDataNode
 | GraphEdge GDataEdge
 deriving (Eq,Show)

-- | The datatype GOAL contains all the information read by the parser from the
-- user
data GOAL = 
   Node         String   
 | Edge         String   String     
 | LabeledEdge  String   Int     String 
 deriving (Eq,Show)


-- | The function 'unite_semicolon' unites a list of strings into one string
-- using a semicolon as separetor
unite_semicolon :: [String] -> String
unite_semicolon input
  = case input of
      x:[] -> x
      x:ls -> x++";"++(unite_semicolon ls)
      []   -> []



-- | The function 'getGoalList' creates a graph goal list ( a graph goal is 
-- defined by the datatype 'GraphGoals') that is a part of the list passed
-- as an argument that corresponds to the parsed goals ( see
-- 'GOAL' datatype)
getGoalList :: [GOAL] -> [GraphGoals] -> [GraphGoals] -> IO [GraphGoals]
getGoalList goalList allg ll 
 = case goalList of
    (Node x):l -> do
      tmp2<- getGoalList l allg ll
      case extractGraphNode x allg of
        Just smth -> return (smth:tmp2)
        Nothing -> do
           putStr ("Couldn't find node "++x++"\n")
           return []
    (Edge x y):l -> do
      tmp <- extractGraphEdge x y allg ll
      tmp2<- getGoalList l allg ll
      case tmp of 
        Just smth -> return (smth:tmp2)
        Nothing -> return tmp2
    (LabeledEdge x nb y):l -> do
      tmp <- extractGraphLabeledEdge x nb y allg ll
      tmp2<- getGoalList l allg ll
      case tmp of
         Just smth -> return (smth:tmp2)
         Nothing -> return tmp2
    [] -> return [] 

 
-- | The function 'extractGraphNode' extracts the goal node defined by 
-- the ID of the node as a string from the provided list of goals  
extractGraphNode :: String -> [GraphGoals] -> Maybe GraphGoals
extractGraphNode x = find ( \ g -> case g of 
    GraphNode (_, label) -> getDGNodeName label == x
    _ -> False)
         
-- | The function 'extractGraphEdge' extracts the goal edge determined by 
-- the two nodes from the provided list of goals
extractGraphEdge:: String -> String -> [GraphGoals] -> [GraphGoals]
                    -> IO (Maybe GraphGoals)
extractGraphEdge x y allGoals ll
   = case allGoals of
      [] -> return  Nothing
      GraphEdge (xx, yy, label) : l ->
         case extractGraphNode x ll of
           Nothing -> do
              putStr ("Couldn't find node "++x++"\n"++
                         "when looking for edge "++x++" -> "++y++"\n")
              return Nothing 
           Just t1 -> do
             case extractGraphNode y ll of 
               Nothing -> do
                  putStr ("Couldn't find node "++y++"\n"++
                            "when looking for edge "++x++" -> "++y++"\n")
                  return Nothing
               Just t2 ->
                  case t1 of 
                    (GraphNode (tmp1_nb, _)) ->
                       case t2 of
                        (GraphNode (tmp2_nb, _)) ->
                          if (tmp1_nb == xx) 
                            then if (tmp2_nb == yy) 
                               then return (Just (GraphEdge (xx,yy,label)))
                               else extractGraphEdge x y l ll
                            else extractGraphEdge x y l ll
                        _ -> extractGraphEdge x y l ll
                    _ -> extractGraphEdge x y l  ll 
      _ : l -> extractGraphEdge x y l ll

-- | Same as above but it tries to extract the edge between the nodes
-- with the given number in the order they are found
extractGraphLabeledEdge:: String -> Int -> String -> 
                          [GraphGoals] -> [GraphGoals] -> IO (Maybe GraphGoals)
extractGraphLabeledEdge x nb y allGoals ll
    = case allGoals of
      [] -> return  Nothing
      GraphEdge (xx, yy, label) : l  ->
        case extractGraphNode x ll of
          Nothing -> do
            putStr ("Couldn't find node "++x++"\n"++
             "when looking for edge "++x++" - "++(show nb)++" -> "++y++"\n")
            return Nothing
          Just t1 -> do
            case extractGraphNode y ll of 
              Nothing -> do
               putStr ("Couldn't find node "++y++"\n"++
                "when looking for edge "++x++" - "++(show nb)++" -> "++y++"\n")
               return Nothing
              Just t2 -> do
                  case t1 of 
                    (GraphNode (tmp1_nb, _)) ->
                       case t2 of
                        (GraphNode (tmp2_nb, _)) ->
                          if (tmp1_nb == xx) 
                            then if (tmp2_nb == yy) 
                               then if (nb==0)  
                                 then return (Just (GraphEdge (xx,yy,label)))
                                 else extractGraphLabeledEdge x (nb-1) y l ll
                               else extractGraphLabeledEdge x nb y l ll
                            else extractGraphLabeledEdge x nb y l ll
                        _ -> extractGraphLabeledEdge x nb y l ll
                    _ -> extractGraphLabeledEdge x nb y l ll 
      _:l -> extractGraphLabeledEdge x nb y l ll


-- | The function 'getEdgeGoals' given a list of edges selects all edges that
-- are goals of the graph and returns them as 'GraphGoals'
getEdgeGoals :: [GDataEdge] -> [GraphGoals]
getEdgeGoals = map GraphEdge .
    filter ( \ (_, _, l) -> case thmLinkStatus $ dgl_type l of
        Just LeftOpen -> True
        _ -> False)

-- | The function 'convToGoal' converts a list of 'GDataNode' 
-- into 'GraphGoals' list
convToGoal:: [GDataNode] -> [GraphGoals]
convToGoal = map GraphNode

-- | The function 'convEdgeToGoal' converts a list of 'GDataEdge' 
-- into 'GraphGoals' list
convEdgeToGoal :: [GDataEdge] -> [GraphGoals]
convEdgeToGoal = map GraphEdge

-- | The function 'getEdgeList' returns from a list of graph goals just the 
-- edge goals as ['GDataEdge']
getEdgeList :: [GraphGoals] -> [GDataEdge]
getEdgeList = foldr (\ g l -> case g of
    GraphEdge x -> x : l
    _ -> l) []

-- | The function 'createAllGoalsList' given a library (defined by LIB_NAME and
-- LibEnv) generates the list of all goals (both edges and nodes) of the graph
-- coresponding to the library
createAllGoalsList :: LIB_NAME->LibEnv -> [GraphGoals]
createAllGoalsList ln libEnv
                    = let dgraph = lookupDGraph ln libEnv
                          edgeGoals = getEdgeGoals (labEdges dgraph)
                          nodeGoals = getNodeGoals (labNodes dgraph)
                      in edgeGoals ++ nodeGoals

-- | The function 'getNodeGoals' given a list of nodes selects all nodes that
-- are goals of the graph and returns them as 'GraphGoals'
getNodeGoals::[GDataNode] -> [GraphGoals]
getNodeGoals = map GraphNode . 
    filter ( \ (_, x) -> isDGRef x || not (hasOpenGoals x) || 
           not (isInternalNode x) && hasOpenConsStatus False x)

-- | The function 'extractGoals' given the list of 'GDataEdge' and
-- the list of goals finds all elemnts of in the first list that are
-- also in the second
extractGoals :: [GDataEdge] -> [GraphGoals] -> [GDataEdge]
extractGoals ls ll = concatMap (flip extractGoal ll) ls

extractGoal :: GDataEdge -> [GraphGoals] -> [GDataEdge]
extractGoal x ls = if any ( \ g -> case g of
    GraphEdge y -> y == x
    _ -> False) ls then [x] else []
