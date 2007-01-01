{- |
Module      :$Header$
Description : utilities for Hets commands
Copyright   : uni-bremen and Razvan Pascanu
Licence     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@iu-bremen.de
Stability   : provisional
Portability : portable

Toghether with PGIP.Common, PGIP.Utils contains all the auxiliary functions
used throughout the interactive interface. The reason for dividing these
functions in two files was that otherwise we would've get a circular 
inclusion (for example Proof.Automatic requieres some of these auxiliary 
functions, but some other functions -- that appear now in PGIP.Common -- 
require some functions from Proof.Automatic)


-} 

module PGIP.Utils where
import Data.Graph.Inductive.Graph
import Logic.Grothendieck
import Static.DevGraph
import Syntax.AS_Library

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



-- | The function 'getGoalList' creates a graph goal list ( a graph goal is 
-- defined by the datatype 'GraphGoals') that is a part of the list passed
-- as an argument that corresponds to the parsed goals ( see
-- 'GOAL' datatype)
getGoalList :: [GOAL] -> [GraphGoals] -> [GraphGoals] -> IO [GraphGoals]
getGoalList goalList allg ll 
 = case goalList of
    (Node x):l -> do
      tmp <- extractGraphNode x allg
      tmp2<- getGoalList l allg ll
      case tmp of
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
extractGraphNode:: String->[GraphGoals]->IO (Maybe GraphGoals)
extractGraphNode x allGoals 
    = case allGoals of
       []              ->do
                           return  Nothing
       (GraphNode (nb,label)):l    -> do
                                        if (( getDGNodeName label)==x) 
                                          then return (Just (GraphNode (nb,label)))
                                          else extractGraphNode x l
       _:l                           -> extractGraphNode x l

         
-- | The function 'extractGraphEdge' extracts the goal edge determined by 
-- the two nodes from the provided list of goals
extractGraphEdge:: String -> String -> [GraphGoals] -> [GraphGoals]
                    -> IO (Maybe GraphGoals)
extractGraphEdge x y allGoals ll
   = case allGoals of
      []             -> do 
                       return  Nothing
      (GraphEdge (xx,yy,label)):l -> do 
         ttt1 <- extractGraphNode x ll
         ttt2 <- extractGraphNode y ll
         case ttt1 of
           Nothing -> do
              putStr ("Couldn't find node "++x++"\n"++
                         "when looking for edge "++x++" -> "++y++"\n")
              return Nothing 
           Just t1 -> do
             case ttt2 of 
               Nothing -> do
                  putStr ("Couldn't find node "++y++"\n"++
                            "when looking for edge "++x++" -> "++y++"\n")
                  return Nothing
               Just t2 -> do
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
      _:l    -> extractGraphEdge x y l ll


-- | Same as above but it tries to extract the edge between the nodes
-- with the given number in the order they are found
extractGraphLabeledEdge:: String -> Int -> String -> 
                          [GraphGoals] -> [GraphGoals] -> IO (Maybe GraphGoals)
extractGraphLabeledEdge x nb y allGoals ll
    = case allGoals of
      []             ->return  Nothing
      (GraphEdge (xx,yy,label)):l  -> do
        ttt1<- extractGraphNode x ll
        ttt2<- extractGraphNode y ll
        case ttt1 of
          Nothing -> do
            putStr ("Couldn't find node "++x++"\n"++
             "when looking for edge "++x++" - "++(show nb)++" -> "++y++"\n")
            return Nothing
          Just t1 -> do
            case ttt2 of 
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
getEdgeGoals ls =
    case ls of
         (x,y,l):ll -> let labelInfo = getDGLinkType l in
                       case labelInfo of
                        "unproventhm"  -> (GraphEdge (x,y,l)):(getEdgeGoals ll)
                        "localunproventhm" -> (GraphEdge (x,y,l)):(getEdgeGoals ll)
                        "hetunproventhm"   -> (GraphEdge (x,y,l)):(getEdgeGoals ll)
                        "hetlocalunproventhm" -> (GraphEdge (x,y,l)):(getEdgeGoals ll)
                        _                     -> getEdgeGoals ll
         []  -> []

-- | The function 'convToGoal' converts a list of 'GDataNode' 
-- into 'GraphGoals' list
convToGoal:: [GDataNode] -> [GraphGoals]
convToGoal ls
 = case ls of
     x:l -> (GraphNode x) : (convToGoal l)
     []  -> []

-- | The function 'convEdgeToGoal' converts a list of 'GDataEdge' 
-- into 'GraphGoals' list
convEdgeToGoal :: [GDataEdge] -> [GraphGoals]
convEdgeToGoal ls 
 = case ls of 
     x:l -> (GraphEdge x): (convEdgeToGoal l)
     []  -> []


-- | The function 'getEdgeList' returns from a list of graph goals just the 
-- edge goals as ['GDataEdge']
getEdgeList :: [GraphGoals] -> [GDataEdge]
getEdgeList ls =
        case ls of 
             (GraphEdge x):l  -> x:(getEdgeList l)
             (GraphNode _):l  -> getEdgeList l
             []               -> []


-- | The function 'getDGLinkType' returns a String describing the type of the edge
getDGLinkType :: DGLinkLab -> String
getDGLinkType lnk = case dgl_morphism lnk of
 GMorphism _ _ _ _ _-> 
  {- if not (is_injective (targetLogic cid) mor) then trace "noninjective morphism found" "hetdef" 
  else -}
   case dgl_type lnk of
    GlobalDef ->
      if isHomogeneous $ dgl_morphism lnk then "globaldef"
          else "hetdef"
    HidingDef -> "hidingdef"
    LocalThm thmLnkState _ _ -> het++"local" ++ getThmType thmLnkState ++ "thm"
    GlobalThm thmLnkState _ _ -> het++getThmType thmLnkState ++ "thm"
    HidingThm _ thmLnkState -> getThmType thmLnkState ++ "hidingthm"
    FreeThm _ bool -> if bool then "proventhm" else "unproventhm"
    _  -> "def" -- LocalDef, FreeDef, CofreeDef
 where het = if isHomogeneous $ dgl_morphism lnk then "" else "het"

getThmType :: ThmLinkStatus -> String
getThmType thmLnkState =
  case thmLnkState of
    Proven _ _ -> "proven"
    LeftOpen -> "unproven"

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
getNodeGoals ls =
   case ls of
     (nb,x):l  -> 
       let labelInfo = getDGNodeType x in
       case labelInfo of
         "open_cons__spec" -> (GraphNode (nb,x)):(getNodeGoals l)
         "proven_cons__spec" -> (GraphNode (nb,x)):(getNodeGoals l)
         "locallyEmpty__open_cons__spec" -> (GraphNode (nb,x)):(getNodeGoals l)
         "open_cons__internal" -> (GraphNode (nb,x)):(getNodeGoals l)
         "proven_cons__internal" -> (GraphNode (nb,x)):(getNodeGoals l)
         "dg_ref"     -> (GraphNode (nb,x)):(getNodeGoals l)
         _            -> getNodeGoals l
     []   -> []

-- | gets the type of a development graph edge as a string
getDGNodeType :: DGNodeLab -> String
getDGNodeType dgnodelab =
    (if hasOpenGoals dgnodelab then "locallyEmpty__"  else "")
    ++ case isDGRef dgnodelab of
       True -> "dg_ref"
       False -> (if hasOpenConsStatus dgnodelab
                 then "open_cons__"
                 else "proven_cons__")
                ++ if isInternalNode dgnodelab
                   then "internal"
                   else "spec"
    where
      hasOpenConsStatus dgn = dgn_cons dgn /= None &&
          case dgn_cons_status dgn of
            LeftOpen -> True
            _ -> False


-- | The function 'extractGoals' given the list of 'GDataEdge' and
-- the list of goals finds all elemnts of in the first list that are
-- also in the second
extractGoals :: [GDataEdge] -> [GraphGoals] -> [GDataEdge]
extractGoals ls ll
 = case ls of 
      []  -> []
      y:l -> ((extractGoal y ll)++(extractGoals l ll))

extractGoal :: GDataEdge -> [GraphGoals] -> [GDataEdge]
extractGoal x ls
  = case ls of
       []                 -> []
       (GraphEdge y):l    -> if (y==x) then [x]
                                 else extractGoal x l
       _:l                -> extractGoal x l
