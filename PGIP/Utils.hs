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
import Common.Result
import Syntax.AS_Library
import Logic.Grothendieck
import Data.List (find , findIndices ,genericIndex )
type GDataEdge = LEdge DGLinkLab
type GDataNode = LNode DGNodeLab

data GraphGoals =
   GraphNode GDataNode (Maybe G_theory)
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

-- | The function 'mapMaybeIO' is a copy of mapMaybe with suport for
-- IO Monad
mapMaybeIO :: (a -> IO (Maybe b)) -> [a] -> IO [b]
mapMaybeIO fn ls 
 = case ls of 
      x:xs  -> do
                cont <- mapMaybeIO fn xs
		val <- fn x
		case val of 
		  Nothing -> return cont
		  Just sm -> return (sm:cont)
      []     -> return []


-- | The function 'getGoalList' creates a graph goal list ( a graph goal is 
-- defined by the datatype 'GraphGoals') that is a part of the list passed
-- as an argument that corresponds to the parsed goals ( see
-- 'GOAL' datatype)
getGoalList :: [GraphGoals] -> [GraphGoals] -> [GOAL] -> IO [GraphGoals]
getGoalList ls ln 
  = mapMaybeIO ( \ g -> case g of
     Node x     -> extractGraphNode x ls
     Edge x y   ->  extractGraphEdge x y ls ln
     LabeledEdge x nb y -> extractGraphLabeledEdge x nb y ls ln)
           
{--
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
--}
-- | The function 'errorMsg' prints on the screen a generic error message
errorMsg::String ->IO()
errorMsg txt
 = do 
    putStr "ERROR : "
    putStrLn txt
    putStrLn "Last command has been ignored!\n"


 
-- | The function 'extractGraphNode' extracts the goal node defined by 
-- the ID of the node as a string from the provided list of goals  
extractGraphNode :: String -> [GraphGoals] -> IO (Maybe GraphGoals)
extractGraphNode x ls = case find ( \ g -> case g of 
    GraphNode (_, label) _ -> getDGNodeName label == x
    _ -> False) ls of
        Nothing -> do
	            errorMsg ("Couldn't find node "++x)
		    return Nothing
	Just sm -> return (Just sm)
         
-- | The function 'extractGraphEdge' extracts the goal edge determined by 
-- the two nodes from the provided list of goals
extractGraphEdge:: String -> String -> [GraphGoals] -> 
                     [GraphGoals]-> IO (Maybe GraphGoals)
extractGraphEdge x y ls ln
 = do
   n1 <- extractGraphNode x ln
   case n1 of
    Just (GraphNode (x_nb, _) _) -> do
      n2 <- extractGraphNode y ln
      case n2 of 
       Just (GraphNode (y_nb,_) _) ->
           return (find ( \ g -> case g of
               GraphEdge (xx, yy, _) -> ( xx == x_nb) && (yy== y_nb)
               _                   -> False) ls)
       _ -> do
          errorMsg ("Couldn't find node "++y)
          return Nothing
    _ -> do 
      errorMsg ("Couldn't find node "++x)
      return Nothing
        
-- | Same as above but it tries to extract the edge between the nodes
-- with the given number in the order they are found
extractGraphLabeledEdge:: String -> Int -> String -> [GraphGoals] ->
                          [GraphGoals] -> IO (Maybe GraphGoals)
extractGraphLabeledEdge x nb y ls ln
 = do
   n1 <- extractGraphNode x ln 
   case n1 of
    Just (GraphNode (x_nb,_) _) -> do
      n2 <- extractGraphNode y ln 
      case n2 of
       Just (GraphNode (y_nb,_) _) -> do
         let l = findIndices (\ g -> case g of
                          GraphEdge (xx,yy,_) -> (xx==x_nb) && (yy == y_nb)
                          _                   -> False ) ls
         return (Just (genericIndex ls (genericIndex l nb)))
       _ -> do
         errorMsg ("Couldn't find node"++x)
         return Nothing
    _ -> do
      errorMsg ("Couldn't find node "++x)
      return Nothing
 
{--
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
                    (GraphNode (tmp1_nb, _) _ _) ->
                       case t2 of
                        (GraphNode (tmp2_nb, _) _ _) ->
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
--}

-- | The function 'getEdgeGoals' given a list of edges selects all edges that
-- are goals of the graph and returns them as 'GraphGoals'
getEdgeGoals :: [GDataEdge] -> [GraphGoals]
getEdgeGoals = map GraphEdge .
    filter ( \ (_, _, l) -> case thmLinkStatus $ dgl_type l of
        Just LeftOpen -> True
        _ -> False)


doTranslationTh :: AnyComorphism -> GraphGoals -> GraphGoals
doTranslationTh comorph x
 = case x of
    GraphNode (x1, (DGNode x2 th x3 x4 x5 x6 x7)) trTh ->
      case trTh of
        Nothing -> 
          case mapG_theory comorph th of
             Result _ (Just nwTh) ->
               GraphNode (x1, (DGNode x2 th x3 x4 x5 x6 x7)) (Just nwTh)
             _ ->
               GraphNode (x1, (DGNode x2 th x3 x4 x5 x6 x7)) trTh
        Just smTh ->
          case mapG_theory comorph smTh of
             Result _ (Just nwTh) ->
               GraphNode (x1, (DGNode x2 th x3 x4 x5 x6 x7)) (Just nwTh)
             _ ->
              GraphNode (x1, (DGNode x2 th x3 x4 x5 x6 x7)) trTh
    GraphNode (x1, (DGRef x2 x3 x4 th x5 x6)) trTh ->
      case trTh of 
        Nothing ->
          case mapG_theory comorph th of
             Result _ (Just nwTh) ->
               GraphNode (x1, (DGRef x2 x3 x4 th x5 x6)) (Just nwTh)
             _ ->
               GraphNode (x1, (DGRef x2 x3 x4 th x5 x6)) trTh
        Just smTh ->
          case mapG_theory comorph smTh of
             Result _ (Just nwTh) ->
               GraphNode (x1, (DGRef x2 x3 x4 th x5 x6)) (Just nwTh)
             _ ->
               GraphNode (x1, (DGRef x2 x3 x4 th x5 x6)) trTh
    _ -> x


useTranslated :: [GraphGoals] -> [GraphGoals] -> [GraphGoals]
useTranslated xs
  = map ( \x -> case x of
            GraphNode (l1, _) _ ->
	      case find ( \ y -> case y of
	         GraphNode (l2, _) _ -> l1 == l2
		 _                   -> False ) xs of
               Nothing -> x
	       Just k  -> k
            _  -> x)


-- | The function 'convToGoal' converts a list of 'GDataNode' 
-- into 'GraphGoals' list
convToGoal:: [GDataNode] -> [GraphGoals]
convToGoal  = 
      map (\x -> GraphNode x Nothing) 

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
getNodeGoals = map (\x -> GraphNode x Nothing) . 
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
