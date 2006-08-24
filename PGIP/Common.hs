{- |
Module      :$Header$
Copyright   : uni-bremen and Razvan Pascanu
Licence     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@iu-bremen.de
Stability   : provisional
Portability : portable

Usefull functions and datatypes for the parser.


   TODO 
       - add comment.

-} 

module PGIP.Common where
                      


import Syntax.AS_Library
import Static.DevGraph
import Proofs.InferBasic
import Common.DocUtils
import Common.Result
import Common.Taxonomy
import GUI.Taxonomy
import GUI.ConvertDevToAbstractGraph
import Data.Maybe
import Data.Graph.Inductive.Graph
import Comorphisms.LogicGraph

type GDataEdge = LEdge DGLinkLab
type GDataNode = LNode DGNodeLab
    
-- The datatype GOAL contains all the information read by the parser from the
-- user
data GOAL = 
   Node         String   
 | Edge         String   String     
 | LabeledEdge  String   Int     String 
 deriving (Eq,Show)


-- The parsed goals will be converted afterwards in GraphGoals meaning they 
-- will store the same information as a graph node or edge
data GraphGoals =
   GraphNode  GDataNode
 | GraphEdge  GDataEdge
 deriving (Eq,Show)     


-- The datatype CmdParam contains all the possible parameters a command of
-- the interface might have. It is used to create one function that returns
-- the parameters after parsing no matter what command is parsed
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


-- The datatype Status contains the current status of the interpeter at any
-- moment in time
data Status = 
   OutputErr  String
 | CmdInitialState
-- Env stores the graph loaded 
 | Env     LIB_NAME LibEnv
-- Selected stores the graph goals selected with Infer Basic command
 | Selected [GraphGoals]
-- AllGoals stores all goals contained by the graph at any moment in time
 | AllGoals [GraphGoals]
-- Comorph stores  a certain comorphism to be used
 | Comorph [String]
-- Prover stores the Id of the prover that needs to be used
 | Prover String
-- Address stores the current library loaded so that the correct promter can
-- be generated
 | Address String


 
-- The function 'extractGraphNode' extracts the goal node defined by 
-- 'x' (the ID of the node as a string) from the provided list of goals  
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
         
-- The function 'extractGraphEdge' extracts the goal edge determined by 
-- 'x' and 'y' nodes from the provided list of goals
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
-- Same as above but it tries to extract the edge between the nodes
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


-- The function 'getGoalList' creates a graph goal list ( a graph goal is 
-- defined by the datatype GraphGoals) that is a part of 'allg' list passed
-- as an argument and corresponds to goalList (a parased goal list, see
-- GOAL datatype)
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




convToGoal:: [GDataNode] -> [GraphGoals]
convToGoal ls
 = case ls of
     x:l -> (GraphNode x) : (convToGoal l)
     []  -> []

-- The function 'getEdgeGoals' given a list of edges selects all edges that
-- are goals of the graph and returns them as GraphGoals
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

-- The function checks if w1 is a prefix of w2
prefix :: String -> String -> Bool
prefix w1 w2 
 = case w1 of 
     x1:l1 -> case w2 of
               x2:l2 -> if (x1==x2) then (prefix l1 l2)
                                    else False
               []    -> False
     [] -> True

-- The function checks if the word 'wd' is a prefix of the name of 
-- any of the nodes in the list, if so it returns the list of the 
-- names otherwise it returns the empty list
checkWord :: String -> [GDataNode] -> String
checkWord wd allNodes
 = case allNodes of
     (_, (DGNode thName _ _ _ _ _ _ )):l -> 
                         if (prefix wd (showName thName))
                                then 
                                  if ((showName thName)=="")
                                     then checkWord wd l
                                     else ((showName thName)++" "++(checkWord wd l))
                                else checkWord wd l
     (_, (DGRef thName _ _ _ _ _)):l -> 
                         if (prefix wd (showName thName))
                                then 
                                  if ((showName thName)=="")
                                     then checkWord wd l
                                     else ((showName thName)++" "++(checkWord wd l))
                                else checkWord wd l
     []                   -> [] 
 
-- The function flips a string around
reverseOrder :: String -> String -> String
reverseOrder ls wd
 = case ls of
      [] ->  wd
      x:l -> reverseOrder l (x:wd)

-- The function categorizes the commands after the
-- type of arguments it should expect
prefixType ::String -> Int
prefixType wd
 = case wd of
     "dg auto" -> 1
     "dg glob-subsume" -> 1
     "dg glob-decomp" -> 1
     "dg loc-infer" -> 1
     "dg loc-decomp" -> 1
     "dg comp" -> 1
     "dg comp-new" -> 1
     "dg hide-thm" -> 1
     "dg basic"  -> 1
     _           -> 0

-- The function checks if a word still has white spaces or not
hasWhiteSpace :: String -> Bool
hasWhiteSpace ls 
 = case ls of
       []    -> False
       ' ':_ -> True
       '\t':_-> True
       '\n':_-> True
       '\r':_-> True
       ';':_ -> True
       '-':_ -> True
       '>':_ -> True
       ',':_ -> True
       _:l   -> hasWhiteSpace l


-- The function tries to obtain only the incomplete word
-- removing the command name
getSuffix :: String -> String
getSuffix wd
 = if (hasWhiteSpace wd) then getSuffix (tail wd)
                         else wd

-- The function given a string tries to obtain the command
-- name and remove the incomplete word from the end
getPrefix :: String -> String -> IO String
getPrefix wd tmp
 = if (hasWhiteSpace wd) 
         then if (hasWhiteSpace (tail wd))
                  then do
                        getPrefix (tail wd) ((head wd):tmp)
                  else if ((prefixType (reverseOrder tmp [])) > 0)
                             then return (reverseOrder tmp [])
                             else getPrefix tmp []
        else return []

-- The function simply adds the 'wd' string as a prefix to any
-- word from the given list
addWords ::[String] -> String -> [String]
addWords ls wd
 = case ls of
      x:l  -> (wd++x):(addWords l wd)
      []   -> []

-- The function 'pgipCompletionFn' given the current status and an incomplete
-- word provides a list of possible words completions
pgipCompletionFn :: [Status] -> String -> IO [String]
pgipCompletionFn state wd
 = case state of
    (Env ln libEnv):_ -> do
        let dgraph= lookupDGraph ln libEnv
        pref <- getPrefix wd []
--        putStr (pref++"\n")
        if ((prefixType pref)> 0) 
         then do
          let list = checkWord (getSuffix wd) (labNodes dgraph)
--          putStr ("::"++(getSuffix wd)++"\n")
          if (list=="") then return []
                        else return (addWords (words list) (pref++" "))
         else
          return []
    _:l               ->    pgipCompletionFn l wd
    []                -> return []

-- The function 'getNodeGoals' given a list of nodes selects all nodes that
-- are goals of teh graph and returns them as GraphGoals
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


-- The function 'createAllGoalsList' given a library (defined by LIB_NAME and
-- LibEnv) generates the list of all goals (both edges and nodes) of the graph
-- coresponding to the library
createAllGoalsList :: LIB_NAME->LibEnv -> [GraphGoals]
createAllGoalsList ln libEnv
                    = let dgraph = lookupDGraph ln libEnv
                          edgeGoals = getEdgeGoals (labEdges dgraph)
                          nodeGoals = getNodeGoals (labNodes dgraph)
                      in edgeGoals ++ nodeGoals

-- The function 'getEdgeList' returns from a list of graph goals just the 
-- edge goals as [GDataEdge]
getEdgeList :: [GraphGoals] -> [GDataEdge]
getEdgeList ls =
        case ls of 
             (GraphEdge x):l  -> x:(getEdgeList l)
             (GraphNode _):l  -> getEdgeList l
             []               -> []
-- The function 'getNodeList' returns from a list of graph goals just
-- the nodes as [GDataNode]
getNodeList :: [GraphGoals] -> [GDataNode]
getNodeList ls =
       case ls of 
            (GraphEdge _):l  -> getNodeList l
            (GraphNode x):l  -> x:(getNodeList l)
            []               -> []

-- The function 'update' returns the updated version of 'status' with the
-- values from 'val' (i.e replaces any value from 'status' with the one from
-- 'val' if they are of the same type otherwise just adds the values from 'val'
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



-- The function 'printNodeTheoryFromList' prints on the screen the theory
-- of all nodes in the [GraphGoals] list
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

-- The function 'printNodeTheory' given a GraphGoal prints on the screen
-- the theory of the node if the goal is a node or 'Not a node !' otherwise
printNodeTheory :: GraphGoals -> IO()
printNodeTheory arg =
  case arg of
   GraphNode (_,(DGNode _ theTh _ _ _ _ _)) -> 
                    putStr  ((showDoc theTh "\n") ++ "\n")
   GraphNode (_,(DGRef _ _ _ theTh _ _)) ->
                    putStr  ((showDoc theTh "\n") ++ "\n")
   _      -> putStr "Not a node!\n" 


-- The function 'findNode' finds to node with the number 'nb' in the goal list
findNode :: Int -> [GDataNode] ->Maybe GraphGoals
findNode nb ls
 = case ls of
           (x,labelInfo):l -> 
                       if (x==nb) then  
                            Just (GraphNode (x,labelInfo))
                                  else
                            findNode nb l
           []  -> Nothing

-- The function 'printInfoFromList' given a GraphGoal list prints the 
-- name of all goals (node or edge)
printInfoFromList :: [GraphGoals] ->[GDataNode]-> IO()
printInfoFromList ls allNodes =
   case ls of
        (GraphNode x):l -> do
              printNodeInfo (GraphNode x)
              putStr "\n"
              result <-printInfoFromList l allNodes
              return result
        (GraphEdge (x,y,_)):l      -> do 
              let x1 = fromJust $ findNode x allNodes
              let y1 = fromJust $ findNode y allNodes
              printNodeInfo x1
              putStr " -> "
              printNodeInfo y1
              putStr "\n"
              result<- printInfoFromList l allNodes
              return result
        []              -> return ()



-- The function 'printNodeInfoFromList' given a GraphGoal list prints the 
-- name of all node goals
printNodeInfoFromList :: [GraphGoals] -> IO()
printNodeInfoFromList ls =
   case ls of
        (GraphNode x):l -> do
              printNodeInfo (GraphNode x)
              putStr "\n"
              result <-printNodeInfoFromList l
              return result
        _:l             -> do 
              result<- printNodeInfoFromList l
              return result
        []              -> return ()
-- The function 'printNodeInfo' given a GraphGoal prints the name of the node
-- if it is a graph node otherwise prints 'Not a node !'
printNodeInfo :: GraphGoals -> IO()
printNodeInfo x =
       case x of
          GraphNode (_, (DGNode tname _ _ _ _ _ _)) -> 
                                        putStr (( showName tname))
          GraphNode (_, (DGRef tname _ _ _ _ _ )) ->
                                        putStr (( showName tname))
          _                          -> putStr "Not a node!\n"

-- The function 'printNodeTaxonomyFromList' given a GraphGoals list generates
-- the 'kind' type of Taxonomy Graphs of all goal nodes from the list
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


-- The function 'printNodeTaxonomy' given just a GraphGoal generates
-- the 'kind' type of Taxonomy Graphs if the goal is a node otherwise
-- it prints on the screen 'Not a node !'
printNodeTaxonomy :: TaxoGraphKind -> GraphGoals -> IO()
printNodeTaxonomy kind x =
   case x of 
     GraphNode (_, (DGNode tname thTh _ _ _ _ _)) -> 
                           displayGraph kind (showName tname) thTh
     GraphNode (_, (DGRef tname _ _ thTh _ _ )) ->
                           displayGraph kind (showName tname) thTh 
     _            -> putStr "Not a node!\n"
        
-- The function proveNodes applies basicInferenceNode for proving to
-- all nodes in the graph goal list
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

