{-# OPTIONS -cpp #-}
{- |
Module      :$Header$
Description : abstract syntax and utilities for Hets commands
Copyright   : uni-bremen and Razvan Pascanu
Licence     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@iu-bremen.de
Stability   : provisional
Portability : portable

Toghether with PGIP.Utils, PGIP.Common contains all the auxiliary functions
used throughout the interactive interface. The reason for dividing these
functions in two files was that otherwise we would've get a circular
inclusion (for example Proof.Automatic requieres some of these auxiliary
functions, but some other functions -- that appear now in PGIP.Common --
require some functions from Proof.Automatic)
-}

module PGIP.Common where

import Syntax.AS_Library
import Static.DevGraph
import Static.DGToSpec

import Logic.Logic
import Logic.Coerce
import Logic.Grothendieck
import Logic.Comorphism
import qualified Logic.Prover as P

#ifdef UNI_PACKAGE
import Events
import Destructible
import GUI.Taxonomy
import Proofs.InferBasic
#endif
import Proofs.EdgeUtils
import Proofs.StatusUtils
import Comorphisms.LogicGraph
import PGIP.Utils

import Common.DocUtils
import Common.Utils
import Common.Result
import Common.Taxonomy
import Common.AS_Annotation
import qualified Common.OrderedMap as OMap

import Data.Graph.Inductive.Graph
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (fromJust)

-- | The datatype 'CmdParam' contains all the possible parameters a command of
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


-- | The datatype 'Status' contains the current status of the interpeter at any
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
 | Comorph AnyComorphism
-- SProver stores the selected prover
 | SProver  G_prover
-- Address stores the current library loaded so that the correct promter can
-- be generated
 | Address String
-- If the flag exists it means that the interpreter expects to read some
-- script
 | LoadScript
-- The string send with MoreScript will be attached at the end of the
-- current script
 | More String
-- The string stored as Script is the current script
 | Script String


-- | The function returns the 'LIB_NAME' stored in the status if any
getLIB_NAME :: [Status] -> Maybe LIB_NAME
getLIB_NAME ls
   = case ls of
        []           -> Nothing
        (Env ln _):_ -> Just ln
        _:l          -> getLIB_NAME l

-- | The function returns the 'LibEnv' stored in the status if any
getLibEnv :: [Status] -> Maybe LibEnv
getLibEnv ls
  = case ls of
      []               -> Nothing
      (Env _ libEnv):_ -> Just libEnv
      _:l              -> getLibEnv l

-- | The function returns the list of selected goals if any
getSelected :: [Status] -> Maybe [GraphGoals]
getSelected ls
  = case ls of
       []                -> Nothing
       (Selected list):_ -> Just list
       _:l               -> getSelected l

-- | The function returns the list of all goals stored in the status if any
getAllGoals :: [Status] -> Maybe [GraphGoals]
getAllGoals ls
  = case ls of
      []                -> Nothing
      (AllGoals list):_ -> Just list
      _:l               -> getAllGoals l

-- | The function returns the text containing the comorphism if any
getComorph :: [Status] -> Maybe AnyComorphism
getComorph ls
  = case ls of
      []                -> Nothing
      (Comorph val):_   -> Just val
      _:l               -> getComorph l

-- | The function return the selected prover if any
getSProver :: [Status]
           -> Maybe G_prover
getSProver ls
  = case ls of
      []              -> Nothing
      (SProver val):_ -> Just val
      _:l             -> getSProver l

-- | The function return the address of the current library loaded if any
getAddress :: [Status] -> Maybe String
getAddress ls
  = case ls of
     []                -> Nothing
     (Address val):_   -> Just val
     _:l               -> getAddress l

-- | The function returns the current Script to use
getScriptStatus :: [Status] -> Maybe String
getScriptStatus ls
  = case ls of
     []             -> Nothing
     (Script val):_ -> Just val
     _:l            -> getScriptStatus l



-- | The function checks if the first string is a prefix of the second.
prefix :: String -> String -> Bool
prefix w1 w2
 = case w1 of
     x1:l1 -> case w2 of
               x2:l2 -> if (x1==x2) then (prefix l1 l2)
                                    else False
               []    -> False
     [] -> True

-- | The function returns the name of all nodes from the given list
getNameList :: [GDataNode] -> [String]
getNameList ls
 = case ls of
     (_, (DGNode thName _ _ _ _ _ _ )):l -> (showName thName):(getNameList l)
     (_, (DGRef  thName _ _ _ _ _ )):l   -> (showName thName):(getNameList l)
     []                                  -> []

-- | The function checks if the word given is a prefix of the name of
-- any of the nodes in the list, if so it returns the list of the
-- names otherwise it returns the empty list
checkWord :: String -> [String] -> [String]
checkWord wd allNodes
 = case allNodes of
     str:l ->
                         if (prefix wd str)
                                then
                                  if (str=="")
                                     then checkWord wd l
                                     else (str:(checkWord wd l))
                                else checkWord wd l
     []                   -> []

-- | The function flips a string around
reverseOrder :: String -> String -> String
reverseOrder ls wd
 = case ls of
      [] ->  wd
      x:l -> reverseOrder l (x:wd)

-- | The function categorizes the commands after the
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
     "dg basic"  -> 3
     "select"    -> 3
     "node-number" -> 2
     "info" -> 3
     "show-concept" -> 2
     "show-taxonomy" -> 2
     "show-theory" -> 2
     "prover" -> 4
     "translate" ->5
     _           -> 0

arrowNext :: String -> Bool
arrowNext ls =
  case ls of
     ' ':l -> arrowNext l
     '-':l -> case l of
                '>':_ -> True
                _ -> False
     _ -> False

afterArrow :: String -> String
afterArrow ls =
    case ls of
      ' ':l -> afterArrow l
      '-':l -> afterArrow l
      '>':l -> afterArrow l
      smth  -> smth

-- | The function checks if a word still has white spaces or not
hasWhiteSpace :: String -> Bool
hasWhiteSpace ls
 = case ls of
       []    -> False
       ' ':l -> if (arrowNext l) then hasWhiteSpace (afterArrow l)
                                 else True
       '\t':_-> True
       '\n':_-> True
       '\r':_-> True
       ';':_ -> True
       ',':_ -> True
       _:l   -> hasWhiteSpace l

-- | The function tries to obtain only the incomplete word
-- removing the command name
getSuffix :: String -> String
getSuffix wd
 = if (hasWhiteSpace wd) then getSuffix (tail wd)
                         else wd

-- | The function given a string tries to obtain the command
-- name and remove the incomplete word from the end
getShortPrefix :: String -> String -> IO String
getShortPrefix wd tmp
 = if (hasWhiteSpace wd)
         then if (hasWhiteSpace (tail wd))
                  then do
                        getShortPrefix (tail wd) ((head wd):tmp)
                  else if ((prefixType (reverseOrder tmp [])) > 0)
                             then return (reverseOrder tmp [])
                             else getShortPrefix (reverseOrder tmp []) []
        else return []

eliminateFirst ::String -> String -> String
eliminateFirst tmp1 tmp2
 = case tmp1 of
      []    -> case tmp2 of
                [] -> []
                t  -> tail t
      _:l   -> eliminateFirst l (tail tmp2)

arrowType :: String -> Bool
arrowType ls
 = case ls of
     '-':l -> case l of
               '>':_ -> True
               _  -> False
     _:l -> arrowType l
     [] -> False

processElements :: String -> String -> IO [String]
processElements input tmp
  = case input of
      ' ':l  -> case tmp of
                   [] -> processElements l tmp
                   _ -> if (arrowNext l)
                            then if (arrowType l)
                                    then processElements (afterArrow l)
                                                    (tmp ++ " -> ")
                                    else processElements (afterArrow l)
                                                    (tmp ++ " - ")
                            else do
                                  t<- processElements l ""
                                  return (tmp : t)
      x:l -> processElements l (tmp ++ [x])
      []  -> return []

getUsedElements :: String -> IO [String]
getUsedElements input
 = do
    tmp1 <- getShortPrefix input ""
    let tmp2 = getLongPrefix input ""
    processElements (eliminateFirst tmp1 tmp2) ""

eliminateElement ::String -> [String] -> [String]
eliminateElement el ls
  = case ls of
     x:l -> if (x==el) then eliminateElement el l
                       else x:(eliminateElement el l)
     [] -> []

eliminateList :: [String] -> [String] -> [String]
eliminateList ls ll
 = case ls of
     x:l -> eliminateList l (eliminateElement x ll)
     []  -> ll

getLongPrefix :: String -> String -> String
getLongPrefix wd tmp
 = if (hasWhiteSpace wd)
          then getLongPrefix (tail wd) ((head wd):tmp)
          else reverseOrder tmp []
-- | The function simply adds the string as a prefix to any
-- word from the given list
addWords ::[String] -> String -> [String]
addWords ls wd
 = case ls of
      x:l  -> (wd++x):(addWords l wd)
      []   -> []

solveNode::[GraphGoals] -> Maybe [AnyComorphism]
solveNode input
 = case input of
    (GraphNode (_,x) olTh):_ ->
      case olTh of
       Just smth -> Just (findComorphismPaths
                           logicGraph (sublogicOfTh smth))
       Nothing ->
        case x of
           DGNode _ th _ _ _ _ _ -> Just (findComorphismPaths
                                           logicGraph (sublogicOfTh th))
           DGRef _ _ _ th _ _ ->    Just (findComorphismPaths
                                           logicGraph (sublogicOfTh th))
    _:ls -> solveNode ls
    []   -> Nothing


solveComorph::[Status] -> Maybe [AnyComorphism]
solveComorph state
  = case getComorph state of
      Just smth  -> Just [smth]
      Nothing    -> case getSelected state of
                      Nothing  -> Nothing
                      Just ls  -> solveNode ls

createProverList :: [(G_prover, AnyComorphism)] -> [String]
createProverList ls
 =
   case ls of
     (x,_):l -> ((getPName x): (createProverList l))
     []      ->  []


getProversCMDLautomatic::[AnyComorphism]->[(G_prover,AnyComorphism)]
getProversCMDLautomatic = foldl addProvers []
     where addProvers acc cm =
             case cm of
             Comorphism cid -> acc ++
                 foldl (\ l p -> if P.hasProverKind P.ProveCMDLautomatic p
                                    then (G_prover (targetLogic cid) p,cm):l
                                    else l)
                       []
                       (provers $ targetLogic cid)

-- | The function 'getComorphismName' given a comorphism returns its name as a
-- string
getComorphismName::AnyComorphism -> String
getComorphismName (Comorphism cid) = language_name cid

-- | The function 'getComorphismNames' given the list of all comorphisms
-- returns a list of names
getComorphismNames ::[AnyComorphism]-> [String]
getComorphismNames ls
  = case ls of
     []   -> []
     x:l  -> (getComorphismName x):(getComorphismNames l)

-- | The function 'pgipCompletionFn' given the current status and an incomplete
-- word provides a list of possible words completions
pgipCompletionFn :: [Status] -> String -> IO [String]
pgipCompletionFn state wd
 =
   case getLIB_NAME state of
    Nothing -> return []
    Just ln ->
     case getLibEnv state of
      Nothing -> return []
      Just libEnv ->
       case getAllGoals state of
        Nothing -> return []
        Just allGoals ->
         do
          let dgraph = lookupDGraph ln libEnv
          pref <- getShortPrefix wd []
          let tmp = case (prefixType pref) of
                     1 -> getGoalNameFromList allGoals
                                                (convToGoal (labNodesDG dgraph))
                     2 -> getNameList (labNodesDG dgraph)
                     3 -> (getNameList (labNodesDG dgraph)) ++
                           (getGoalNameFromList allGoals
                                                (convToGoal (labNodesDG dgraph)))
                     4 -> case solveComorph state of
                             Nothing   -> []
                             Just smth -> createProverList
                                (getProversCMDLautomatic smth)
                     5 -> getComorphismNames comorphismList
                     _ -> []
          usedElem <- getUsedElements wd
          let values = eliminateList usedElem tmp
          let list = checkWord (getSuffix wd) values
          if (list == [])
               then return []
               else return (addWords list (getLongPrefix wd []))



{--
-- | The function 'getNodeList' returns from a list of graph goals just
-- the nodes as ['GDataNode']
getNodeList :: [GraphGoals] -> [GDataNode]
getNodeList ls =
       case ls of
            (GraphEdge _):l  -> getNodeList l
            (GraphNode x _):l  -> x:(getNodeList l)
            []               -> []
--}
-- | The function 'update' returns the updated version of the status defined in
-- the second argument with the values from the first argument (i.e replaces
-- any value from status with the one from val if they are of the same type
-- otherwise just adds the new values
update::[Status] -> [Status]
            -> IO [Status]
update val status
 = case val of
    []                  ->  return  status
    (Env x y):l         ->
      case status of
       []                 -> update l [Env x y]
       CmdInitialState:ls -> update ((Env x y):l) ls
       (OutputErr xx):ls   -> do
                              errorMsg xx
                              update ((Env x y):l) ls
       (Env _ _):ls       -> update l ((Env x y):ls)
       (Selected xx):ls   -> do
                             nextStep <- update [Env x y] ls
                             update l ((Selected xx):nextStep)
       (AllGoals xx):ls   -> do
                             nextStep <- update [Env x y] ls
                             update l ((AllGoals xx):nextStep)
       (Comorph xx):ls    -> do
                             nextStep <- update [Env x y] ls
                             update l ((Comorph xx):nextStep)
       (SProver xx):ls    -> do
                             nextStep <- update [Env x y] ls
                             update l ((SProver xx):nextStep)
       (Address xx):ls    -> do
                             nextStep <- update [Env x y] ls
                             update l ((Address xx):nextStep)
       LoadScript:ls      -> do
                             nextStep <- update [Env x y] ls
                             update l (LoadScript:nextStep)
       (More xx):ls       -> do
                             nextStep <- update [Env x y] ls
                             update l ((More xx):nextStep)
       (Script xx):ls     -> do
                             nextStep <- update [Env x y] ls
                             update l ((Script xx):nextStep)
    (Selected x):l ->
      case status of
       []                 -> update l [Selected x]
       CmdInitialState:ls -> update ((Selected x):l) ls
       (OutputErr xx):ls   -> do
                              errorMsg xx
                              update ((Selected x):l) ls
       (Env xx yy):ls     -> do
                             nextStep <- update [Selected x] ls
                             update l ((Env xx yy):nextStep)
       (Selected _):ls    -> update l ((Selected x):ls)
       (AllGoals xx):ls   -> do
                             nextStep <- update [Selected x] ls
                             update l ((AllGoals xx):nextStep)
       (Comorph xx):ls    -> do
                             nextStep <- update [Selected x] ls
                             update l ((Comorph xx):nextStep)
       (SProver xx):ls    -> do
                             nextStep <- update [Selected x] ls
                             update l ((SProver xx):nextStep)
       (Address xx):ls    -> do
                             nextStep <- update [Selected x] ls
                             update l ((Address xx):nextStep)
       LoadScript:ls      -> do
                             nextStep <- update [Selected x] ls
                             update l (LoadScript:nextStep)
       (More xx):ls       -> do
                             nextStep <- update [Selected x] ls
                             update l ((More xx):nextStep)
       (Script xx):ls     -> do
                             nextStep <- update [Selected x] ls
                             update l ((Script xx):nextStep)
    (AllGoals x):l ->
      case status of
       []                 -> update  l [AllGoals x]
       CmdInitialState:ls -> update  ((AllGoals x):l) ls
       (OutputErr xx):ls   -> do
                              errorMsg xx
                              update ((AllGoals x):l) ls
       (Env xx yy):ls     -> do
                             nextStep <- update [AllGoals x] ls
                             update l ((Env xx yy):nextStep)
       (Selected xx):ls   -> do
                             nextStep <- update [AllGoals x] ls
                             update l ((Selected xx):nextStep)
       (AllGoals _):ls    -> update l ((AllGoals x):ls)
       (Comorph xx):ls    -> do
                             nextStep <- update [AllGoals x] ls
                             update l ((Comorph xx):nextStep)
       (SProver xx):ls    -> do
                             nextStep <- update [AllGoals x] ls
                             update l ((SProver xx):nextStep)
       (Address xx):ls    -> do
                             nextStep <- update [AllGoals x] ls
                             update l ((Address xx):nextStep)
       LoadScript:ls      -> do
                             nextStep <- update [AllGoals x] ls
                             update l (LoadScript:nextStep)
       (More xx):ls       -> do
                             nextStep <- update [AllGoals x] ls
                             update l ((More xx):nextStep)
       (Script xx):ls     -> do
                             nextStep <- update [AllGoals x] ls
                             update l ((Script xx):nextStep)
    (Comorph x):l ->
      case status of
       []                 -> update l [Comorph x]
       CmdInitialState:ls -> update ((Comorph x):l) ls
       (OutputErr xx):ls   -> do
                              errorMsg xx
                              update ((Comorph x):l) ls
       (Env xx yy):ls     -> do
                             nextStep <- update [Comorph x] ls
                             update l ((Env xx yy):nextStep)
       (Selected xx):ls   -> do
                             nextStep <- update [Comorph x] ls
                             update l ((Selected xx):nextStep)
       (AllGoals xx):ls   -> do
                             nextStep <- update [Comorph x] ls
                             update l ((AllGoals xx):nextStep)
       (Comorph _):ls     -> update l ((Comorph x):ls)
       (SProver xx):ls    -> do
                             nextStep <- update [Comorph x] ls
                             update l ((SProver xx):nextStep)
       (Address xx):ls    -> do
                             nextStep <- update [Comorph x] ls
                             update l ((Address xx):nextStep)
       LoadScript:ls      -> do
                             nextStep <- update [Comorph x] ls
                             update l (LoadScript:nextStep)
       (More xx):ls       -> do
                             nextStep <- update [Comorph x] ls
                             update l ((More xx):nextStep)
       (Script xx):ls     -> do
                             nextStep <- update [Comorph x] ls
                             update l ((Script xx):nextStep)
    (SProver x):l    ->
      case status of
       []                 -> update l [SProver x]
       CmdInitialState:ls -> update ((SProver x):l) ls
       (OutputErr xx):ls   -> do
                              errorMsg xx
                              update ((SProver x):l) ls
       (Env xx yy):ls     -> do
                             nextStep <- update [SProver x] ls
                             update l ((Env xx yy):nextStep)
       (Selected xx):ls   -> do
                             nextStep <- update [SProver x] ls
                             update l ((Selected xx):nextStep)
       (AllGoals xx):ls   -> do
                             nextStep <- update [SProver x] ls
                             update l ((AllGoals xx):nextStep)
       (Comorph xx):ls    -> do
                             nextStep <- update [SProver x] ls
                             update l ((Comorph xx):nextStep)
       (SProver _):ls     -> update l ((SProver x):ls)
       (Address xx):ls    -> do
                             nextStep <- update [SProver x] ls
                             update l ((Address xx):nextStep)
       LoadScript:ls      -> do
                             nextStep <- update [SProver x] ls
                             update l (LoadScript:nextStep)
       (More xx):ls       -> do
                             nextStep <- update [SProver x] ls
                             update l ((More xx):nextStep)
       (Script xx):ls     -> do
                             nextStep <- update [SProver x] ls
                             update l ((Script xx):nextStep)
    (Address x):l   ->
      case status of
       []                 -> update l [Address x]
       CmdInitialState:ls -> update ((Address x):l) ls
       (OutputErr xx):ls   -> do
                              errorMsg xx
                              update ((Address x):l) ls
       (Env xx yy):ls     -> do
                             nextStep <- update [Address x] ls
                             update l ((Env xx yy):nextStep)
       (Selected xx):ls   -> do
                             nextStep <- update [Address x] ls
                             update l ((Selected xx):nextStep)
       (AllGoals xx):ls   -> do
                             nextStep <- update [Address x] ls
                             update l ((AllGoals xx):nextStep)
       (Comorph xx):ls    -> do
                             nextStep <- update [Address x] ls
                             update l ((Comorph xx):nextStep)
       (SProver xx):ls    -> do
                             nextStep <- update [Address x] ls
                             update l ((SProver xx):nextStep)
       (Address _):ls     -> update l ((Address x):ls)
       LoadScript:ls      -> do
                             nextStep <- update [Address x] ls
                             update l (LoadScript:nextStep)
       (More xx):ls       -> do
                             nextStep <- update [Address x] ls
                             update l ((More xx):nextStep)
       (Script xx):ls     -> do
                             nextStep <- update [Address x] ls
                             update l ((Script xx):nextStep)
    LoadScript:l   ->
      case status of
       []                 -> update l [LoadScript]
       CmdInitialState:ls -> update (LoadScript:l) ls
       (OutputErr xx):ls   -> do
                              errorMsg xx
                              update (LoadScript:l) ls
       (Env xx yy):ls     -> do
                             nextStep <- update [LoadScript] ls
                             update l ((Env xx yy):nextStep)
       (Selected xx):ls   -> do
                             nextStep <- update [LoadScript] ls
                             update l ((Selected xx):nextStep)
       (AllGoals xx):ls   -> do
                             nextStep <- update [LoadScript] ls
                             update l ((AllGoals xx):nextStep)
       (Comorph xx):ls    -> do
                             nextStep <- update [LoadScript] ls
                             update l ((Comorph xx):nextStep)
       (SProver xx):ls    -> do
                             nextStep <- update [LoadScript] ls
                             update l ((SProver xx):nextStep)
       (Address xx):ls    -> do
                             nextStep <- update [LoadScript] ls
                             update l ((Address xx):nextStep)
       LoadScript:ls      -> update l ls
       (More xx):ls       -> do
                             nextStep <- update [LoadScript] ls
                             update l ((More xx):nextStep)
       (Script xx):ls     -> do
                             nextStep <- update [LoadScript] ls
                             update l ((Script xx):nextStep)
    (More x):l       ->
      case status of
       []                 -> update l [Script x]
       CmdInitialState:ls -> update ((More x):l) ls
       (OutputErr xx):ls   -> do
                              errorMsg xx
                              update ((More x):l) ls
       (Env xx yy):ls     -> do
                             nextStep <- update [More x] ls
                             update l ((Env xx yy):nextStep)
       (Selected xx):ls   -> do
                             nextStep <- update [More x] ls
                             update l ((Selected xx):nextStep)
       (AllGoals xx):ls   -> do
                             nextStep <- update [More x] ls
                             update l ((AllGoals xx):nextStep)
       (Comorph xx):ls    -> do
                             nextStep <- update [More x] ls
                             update l ((Comorph xx):nextStep)
       (SProver xx):ls    -> do
                             nextStep <- update [More x] ls
                             update l ((SProver xx):nextStep)
       (Address xx):ls    -> do
                             nextStep <- update [More x] ls
                             update l ((Address xx):nextStep)
       LoadScript:ls      -> do
                             nextStep <- update [More x] ls
                             update l (LoadScript:nextStep)
       (More _):ls       -> do
                            nextStep <- update [More x] ls
                            update l nextStep
       (Script xx):ls     -> update l ((Script (xx++x)):ls)
    (Script x):l       ->
      case status of
       []                 -> update l [Script x]
       CmdInitialState:ls -> update ((Script x):l) ls
       (OutputErr xx):ls   -> do
                              errorMsg xx
                              update ((Script x):l) ls
       (Env xx yy):ls     -> do
                             nextStep <- update [Script x] ls
                             update l ((Env xx yy):nextStep)
       (Selected xx):ls   -> do
                             nextStep <- update [Script x] ls
                             update l ((Selected xx):nextStep)
       (AllGoals xx):ls   -> do
                             nextStep <- update [Script x] ls
                             update l ((AllGoals xx):nextStep)
       (Comorph xx):ls    -> do
                             nextStep <- update [Script x] ls
                             update l ((Comorph xx):nextStep)
       (SProver xx):ls    -> do
                             nextStep <- update [Script x] ls
                             update l ((SProver xx):nextStep)
       (Address xx):ls    -> do
                             nextStep <- update [Script x] ls
                             update l ((Address xx):nextStep)
       LoadScript:ls      -> do
                             nextStep <- update [Script x] ls
                             update l (LoadScript:nextStep)
       (More xx):ls       -> do
                             nextStep <- update [Script x] ls
                             update l ((More xx):nextStep)
       (Script _):ls      -> update l ((Script x):ls)
    (OutputErr xx):l   -> do
                              errorMsg xx
                              update l status
    CmdInitialState:l     -> update l status

-- | The function 'printNodeTheoryFromList' prints on the screen the theory
-- of all nodes in the ['GraphGoals'] list
printNodeTheoryFromList :: [GraphGoals]->  IO()
printNodeTheoryFromList ls =
    case ls of
       (GraphNode x y):l -> do
                           printNodeTheory (GraphNode x y)
                           result<- printNodeTheoryFromList l
                           return result
       _:l   -> do
                  result <-printNodeTheoryFromList l
                  return result
       []    -> return ()

-- | The function 'printNodeTheory' given a 'GraphGoals' prints on the screen
-- the theory of the node if the goal is a node or Not a node ! otherwise
printNodeTheory :: GraphGoals -> IO()
printNodeTheory arg =
  case arg of
   GraphNode (_,(DGNode _ theTh _ _ _ _ _)) othTh ->
         case othTh of
              Nothing ->
                    putStr  ((showDoc theTh "\n") ++ "\n")
              Just smth ->
                    putStr ((showDoc smth "\n") ++ "\n")
   GraphNode (_,(DGRef _ _ _ theTh _ _)) othTh ->
         case othTh of
             Nothing ->
                    putStr  ((showDoc theTh "\n") ++ "\n")
             Just smth ->
                    putStr ((showDoc smth "\n") ++ "\n")
   _      -> putStr "Not a node!\n"

-- | The function 'findNode' finds the node by number in the goal list
findNode :: Int -> [GraphGoals] ->Maybe GraphGoals
findNode nb ls
 = case ls of
           (GraphNode (x,labelInfo) th)  :l ->
                       if (x==nb) then
                            Just (GraphNode (x,labelInfo) th)
                                  else
                            findNode nb l
           _:l      ->  findNode nb l
           []  -> Nothing

-- | The function returns the name of all goals from the list (it
-- requires all the nodes from the graph as a parameter as well)
getGoalNameFromList :: [GraphGoals] -> [GraphGoals] -> [String]
getGoalNameFromList ls allNodes =
  case ls of
       (GraphNode x y):l -> (getGoalName (GraphNode x y)):
                               (getGoalNameFromList l allNodes)
       (GraphEdge (x,y,_)):l ->
                     let x1 = fromJust $ findNode x allNodes
                         y1 = fromJust $ findNode y allNodes
                     in ((getGoalName x1)++" -> "++(getGoalName y1)):
                              (getGoalNameFromList l allNodes)
       []              -> []

-- | The function returns the name of the goal if it is a node
getGoalName ::GraphGoals -> String
getGoalName x
 = case x of
       (GraphNode (_,(DGNode thName _ _ _ _ _ _)) _) -> showName thName
       (GraphNode (_,(DGRef  thName _ _ _ _ _)) _)   -> showName thName
       _                                           -> "Not a node !"

-- | The function 'printInfoFromList' given a GraphGoal list prints the
-- name of all goals (node or edge)
printNamesFromList :: [GraphGoals] ->[GraphGoals]-> IO()
printNamesFromList ls allNodes =
   case ls of
        (GraphNode x y):l -> do
              printNodeInfo (GraphNode x y)
              putStr "\n"
              result <-printNamesFromList l allNodes
              return result
        (GraphEdge (x,y,_)):l      -> do
              let x1 = fromJust $ findNode x allNodes
              let y1 = fromJust $ findNode y allNodes
              printNodeInfo x1
              putStr " -> "
              printNodeInfo y1
              putStr "\n"
              result<- printNamesFromList l allNodes
              return result
        []              -> return ()

-- | The function prints the number of all nodes provided as
-- graph goals
printNodeNumberFromList :: [GraphGoals]-> IO()
printNodeNumberFromList ls =
  case ls of
     (GraphNode x y):l -> do
               printNodeNumber (GraphNode x y)
               putStr "\n"
               result <- printNodeNumberFromList l
               return result
     _:l        -> do
               result <- printNodeNumberFromList l
               return result
     []         -> return ()

-- | The function prints the number of the graph goal if it is a node
printNodeNumber:: GraphGoals -> IO()
printNodeNumber x =
  case x of
     GraphNode (nb, (DGNode tname _ _ _ _ _ _)) _ ->
        putStr ("Node "++(showName tname)++" has number "++(show nb))
     GraphNode (nb, (DGRef tname _ _ _ _ _)) _ ->
                  putStr ("Node "++(showName tname)++" has number "++(show nb))
     _               -> putStr "Not a node !\n"

-- | The function 'printInfoFromList' given a 'GraphGoal' list prints the
-- name of all node goals
printInfoFromList :: [GraphGoals] -> [GraphGoals] -> IO()
printInfoFromList ls allNodes=
   case ls of
        (GraphNode x y):l -> do
              putStr "Name : "
              printNodeInfo (GraphNode x y)
              putStr "\n"
              putStr "Origin : "
              printNodeOrigin (GraphNode x y)
              putStr "\n"
              putStr "Sublogic : "
              printNodeSublogic (GraphNode x y)
              putStr "\n"
              putStr "Number of axioms : "
              printNodeNumberAxioms (GraphNode x y)
              putStr "\n"
              putStr "Number of symbols in the signature : "
              printNodeNumberSymbols (GraphNode x y)
              putStr "\n"
              putStr "Number of unproven theorems : "
              printNodeNumberUnprovenThm (GraphNode x y)
              putStr "\n"
              putStr "Number of proven theorems : "
              printNodeNumberProvenThm (GraphNode x y)
              putStr "\n\n"
              result <-printInfoFromList l allNodes
              return result
        (GraphEdge (x,y,labelData)):l      -> do
              let x1 = fromJust $ findNode x allNodes
              let y1 = fromJust $ findNode y allNodes
              putStr "Name : "
              printNodeInfo x1
              putStr " -> "
              printNodeInfo y1
              putStr "\n"
              putStr "Origin : "
              printEdgeOrigin (GraphEdge (x,y,labelData))
              putStr "\n"
              putStr "Sublogic of source : "
              printNodeSublogic x1
              putStr "\n"
              putStr "Sublogic of target : "
              printNodeSublogic y1
              putStr "\n"
              putStr "Homogeneous : "
              printEdgeHomogeneous (GraphEdge (x,y,labelData))
              putStr "\n"
              putStr "Type : "
              printEdgeType (GraphEdge (x,y,labelData))
              putStr "\n\n"
              result<- printInfoFromList l allNodes
              return result
        []              -> return ()
-- | The function 'printNodeInfo' given a 'GraphGoal' prints the name of the
-- node if it is a graph node otherwise prints Not a node !
printNodeInfo :: GraphGoals -> IO()
printNodeInfo x =
       case x of
          GraphNode (_, (DGNode tname _ _ _ _ _ _)) _ ->
                                        putStr (( showName tname))
          GraphNode (_, (DGRef tname _ _ _ _ _ )) _ ->
                                        putStr (( showName tname))
          _                          -> putStr "Not a node!\n"

-- | The function, give an edge as a graph goal prints the type of the edge
printEdgeType :: GraphGoals -> IO()
printEdgeType x =
  case x of
    GraphEdge (_,_,dglab) ->
       case (getDGLinkType dglab) of
           "globaldef"   -> putStr "global definition"
           "def"         -> putStr "local definition"
           "hidingdef"   -> putStr "hiding definitions"
           "hetdef"      -> putStr "het definition"
           "proventhm"   -> putStr "global proven theorem"
           "unproventhm" -> putStr "global unproven theorem"
           "localproventhm" ->putStr "local proven theorem"
           "localunproventhm" -> putStr "local unproven theorem"
           "hetproventhm"   -> putStr "het global proven theorem"
           "hetunproventhm" -> putStr "het global unproven theorem"
           "hetlocalproventhm" -> putStr "het local proven theorem"
           "hetlocalunproventhm" -> putStr "het local unproven theorem"
           "unprovenhidingthm" -> putStr "unproven hiding theorem"
           "provenhidingthm" -> putStr "proven hiding theorem"
           _                 -> putStr "unknown type"
    _ -> putStr "Not an edge !"

-- | The function give an edge as a graph goal prints the origin of the edge
printEdgeOrigin :: GraphGoals -> IO ()
printEdgeOrigin x =
  case x of
     GraphEdge(_, _, (DGLink _ _ tOrigin _)) ->
          putStr $ show tOrigin
     _ -> putStr "No origin found !"

-- | The function given an edge as a graph goal prints True if it is
-- homogeneaus and false otherwise
printEdgeHomogeneous :: GraphGoals -> IO()
printEdgeHomogeneous x =
  case x of
     GraphEdge (_, _ ,(DGLink tmorph _ _ _)) ->
            if (isHomogeneous tmorph) then putStr "True"
                                      else putStr "False"
     _        -> putStr "Not an edge !"

-- | The function prints the origin of the node given as graph goal
printNodeOrigin :: GraphGoals -> IO()
printNodeOrigin x =
  case x of
    GraphNode (_ ,(DGNode _ _ _ _ torigin _ _)) _ ->
                putStr (show torigin)
    _        -> putStr "Node does not have an origin"

-- | The function prints the sublogic of the node given as graph goal
printNodeSublogic :: GraphGoals -> IO ()
printNodeSublogic x =
  case x of
     GraphNode (_, (DGNode _ tTh _ _ _ _ _)) nwTh->
          case nwTh of
           Nothing ->
              putStr (show (sublogicOfTh tTh))
           Just smth ->
              putStr (show (sublogicOfTh smth))
     GraphNode (_, (DGRef _ _ _ tTh _ _)) nwTh->
          case nwTh of
           Nothing ->
              putStr (show (sublogicOfTh tTh))
           Just smth ->
              putStr (show (sublogicOfTh smth))
     _ -> putStr "Node does not have a sublogic"

-- | The funcion prints the number of axioms of the node given as graph goal
printNodeNumberAxioms :: GraphGoals -> IO ()
printNodeNumberAxioms input =
  case input of
    GraphNode (_, (DGNode _ (G_theory x y _ _ _) _ _ _ _ _)) nwTh ->
     case nwTh of
      Just (G_theory nx ny _ _ _) ->
         putStr $ show (Set.size(sym_of nx ny))
      _ ->
         putStr $ show (Set.size(sym_of x y))
    GraphNode (_, (DGRef _ _ _ (G_theory x y _ _ _) _ _)) nwTh ->
     case nwTh of
      Just (G_theory nx ny _ _ _) ->
         putStr $ show (Set.size (sym_of nx ny))
      Nothing ->
         putStr $ show (Set.size (sym_of x y))
    _ -> putStr "Not a node ! \n"


-- | The function checks if a list is emty or not (same as null)
emtyList :: forall a.[a] -> Bool
emtyList ls =
  case ls of
      [] -> True
      _  -> False

-- | The function adds to the given number the number of symbols found in the
-- given list (sentences from the theory of the node)
countSymbols :: [P.SenStatus a b]->Int -> Int
countSymbols ls nb
 = case ls of
       [] -> nb
       x:l -> if isAxiom x  then countSymbols l (nb+1)
                             else countSymbols l nb

-- | The function adds to the given number the number of unproven theorems
-- found in the list
countUnprovenThm :: [P.SenStatus a b] -> Int -> Int
countUnprovenThm ls nb
 = case ls of
       []   -> nb
       x:l  -> if (emtyList (P.thmStatus x)) then countUnprovenThm l (nb+1)
                                  else countUnprovenThm l nb

-- | The function adds to the given number the number of proven theorems
-- found in the list
countProvenThm :: [P.SenStatus a b] -> Int -> Int
countProvenThm ls nb
 = case ls of
    []  -> nb
    x:l -> if (emtyList (P.thmStatus x)) then countProvenThm l nb
                                             else countProvenThm l (nb+1)

-- | From a list of sentences and SenStatus the function returns only
-- the list of SenStatus
extractSenStatus :: [(String, P.SenStatus a b)] -> [P.SenStatus a b]
extractSenStatus ls =
  case ls of
      []       ->  []
      (_,b):l  ->  b:(extractSenStatus l)

-- | The function prints the number of symbols of the node theory given
-- as a graph goal
printNodeNumberSymbols :: GraphGoals ->  IO ()
printNodeNumberSymbols input =
  case input of
      GraphNode (_, (DGNode _ (G_theory _ _ _ x _) _ _ _ _ _)) nwTh ->
       case nwTh of
        Just (G_theory _ _ _ nx _) ->
           putStr $ show (countSymbols (extractSenStatus (OMap.toList nx)) 0)
        Nothing ->
           putStr $ show (countSymbols (extractSenStatus (OMap.toList x)) 0)
      GraphNode (_, (DGRef _ _ _ (G_theory _ _ _ x _) _ _)) nwTh->
       case nwTh of
         Just (G_theory _ _ _ nx _) ->
           putStr $ show (countSymbols (extractSenStatus (OMap.toList nx)) 0)
         Nothing ->
           putStr $ show (countSymbols (extractSenStatus (OMap.toList x)) 0)
      _  -> putStr "Not a node ! \n"

-- | The function prints the number of unproven theorems of the node theory
-- given as a graph goal
printNodeNumberUnprovenThm :: GraphGoals -> IO ()
printNodeNumberUnprovenThm input =
 case input of
     GraphNode (_, (DGNode _ (G_theory _ _ _ x _) _ _ _ _ _)) nwTh ->
      case nwTh of
       Just (G_theory _ _ _ nx _) ->
        putStr $ show (countUnprovenThm (extractSenStatus (OMap.toList nx)) 0)
       _ ->
        putStr $ show (countUnprovenThm (extractSenStatus (OMap.toList x)) 0)
     GraphNode (_, (DGRef _ _ _ (G_theory _ _ _ x _) _ _)) nwTh ->
      case nwTh of
       Just (G_theory _ _ _ nx _) ->
        putStr $ show (countUnprovenThm (extractSenStatus (OMap.toList nx)) 0)
       _ ->
        putStr $ show (countUnprovenThm (extractSenStatus (OMap.toList x)) 0)
     _  -> putStr "Not a node ! \n"

-- | The function prints the number of proven theorems of the node theory
-- given as a graph goal
printNodeNumberProvenThm :: GraphGoals -> IO ()
printNodeNumberProvenThm input =
 case input of
     GraphNode (_, (DGNode _ (G_theory _ _ _ x _) _ _ _ _ _)) nwTh->
      case nwTh of
       Just (G_theory _ _ _ nx _) ->
        putStr $ show (countProvenThm (extractSenStatus (OMap.toList nx)) 0)
       _ ->
        putStr $ show (countProvenThm (extractSenStatus (OMap.toList x)) 0)
     GraphNode (_, (DGRef _ _ _ (G_theory _ _ _ x _) _ _)) nwTh ->
      case nwTh of
       Just (G_theory _ _ _ nx _) ->
        putStr $ show (countProvenThm (extractSenStatus (OMap.toList nx)) 0)
       _ ->
        putStr $ show (countProvenThm (extractSenStatus (OMap.toList x)) 0)
     _  -> putStr "Not a node ! \n"

-- | The function 'printNodeTaxonomyFromList' given a GraphGoals list generates
-- the 'TaxoGraphKind' type of Taxonomy Graphs of all goal nodes from the list
printNodeTaxonomyFromList :: TaxoGraphKind -> [GraphGoals] -> LibEnv
                          -> LIB_NAME -> IO()
printNodeTaxonomyFromList kind ls libEnv ln =
             case ls of
                   (GraphNode x y): l ->
                       do
                          printNodeTaxonomy kind (GraphNode x y) libEnv ln
                          result <- printNodeTaxonomyFromList kind l libEnv ln
                          return result
                   _ : l ->
                       do
                          result <- printNodeTaxonomyFromList kind l libEnv ln
                          return result
                   []  -> return ()

-- | The function 'printNodeTaxonomy' given just a 'GraphGoals' generates
-- the 'TaxoGraphKind' type of Taxonomy Graphs if the goal is a node otherwise
-- it prints on the screen Not a node !
printNodeTaxonomy :: TaxoGraphKind -> GraphGoals -> LibEnv -> LIB_NAME ->IO()
printNodeTaxonomy kind x libEnv ln =
   case x of
#ifdef UNI_PACKAGE
     GraphNode (n, dgn) _-> do
       case computeTheory libEnv ln n of
         Result _ (Just thTh) ->
             do graph <- displayGraph kind (showName $ dgn_name dgn) thTh
                case graph of
                  Just g -> sync (destroyed g)
                  _ -> return ()
         Result _ _ -> putStrLn "Error computing the theory of the node!"
#endif
     _ -> putStrLn "Not a node! (or compiled without uni)"

-- | mark all newly proven goals with their proof tree
markProved :: (Ord a, Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree) =>
       AnyComorphism -> lid -> [P.Proof_status proof_tree]
    -> P.ThSens a (AnyComorphism,BasicProof)
    -> P.ThSens a (AnyComorphism,BasicProof)
markProved c lid status thSens = foldl upd thSens status
    where upd m pStat = OMap.update (updStat pStat) (P.goalName pStat) m
          updStat ps s = Just
                s { senAttr = P.ThmStatus $
                    (c, BasicProof lid ps) : P.thmStatus s
                  }

-- | The function 'proveNodes' applies 'basicInferenceNode' for proving to
-- all nodes in the graph goal list
proveNodes :: [GraphGoals] ->G_prover -> LIB_NAME ->LibEnv -> [GraphGoals]
           -> IO ([GraphGoals],LibEnv)
proveNodes ls prover ln libEnv addTo = case ls of
#ifdef UNI_PACKAGE
    GraphNode (nb, label) nwTh : l -> do
      let dGraph = lookupDGraph ln libEnv
          thForProof = case nwTh of
                                Just sm-> sm
                                Nothing-> case label of
                                           DGNode _ sm _ _  _ _ _ -> sm
                                           DGRef  _ _  _ sm _ _ -> sm
             -- let G_theory lid1 sig ind thSens _ = thForProof
      case thForProof of
        G_theory lid1 sig ind thSens _ -> do
             --let thForProof@(G_theory lid1 sig ind thSens _) = thForProof
          let nodeName = case label of
                              DGNode sm _ _ _ _ _ _ -> sm
                              DGRef  sm _ _ _ _ _   -> sm
              thName = shows (getLIB_ID ln) "_" ++ showName nodeName

             --  Proving
          case prover of
            G_prover plid p -> do
             -- coerce to prover lid
              let (aMap,gMap) = Map.partition(isAxiom . OMap.ele) thSens
              ths <- coerceThSens lid1 lid1
                          "PGIP.Common.proveNodes : selected goals" gMap
              let (sel_goals, other_goals) =
                              let selected k _ = Set.member k Set.empty
                              in Map.partitionWithKey selected ths
                  provenThs = Map.filter ( \ x -> isProvenSenStatus $
                                           OMap.ele x ) other_goals
                  sel_provenThs = OMap.map ( \ x -> x { isAxiom=True }) $
                                 filterMapWithList (OMap.keys gMap) provenThs
                  sel_sens = filterMapWithList (OMap.keys aMap) thSens
              bTh' <- coerceBasicTheory lid1 lid1
                          "PGIP.Common.proveNodes : basic theory"
                                (sig, P.toNamedList $
                                Map.union sel_sens $
                                Map.union sel_provenThs sel_goals)
              let (sign'',sens'') = bTh'
              p' <- coerceProver plid lid1 "" p
             -- apply function ?!
              case (P.proveCMDLautomatic p') of
                Nothing ->  proveNodes l prover ln libEnv addTo
                Just fn -> do
                  ps <- fn thName (P.Tactic_script "")
                                      $ P.Theory sign'' $ P.toThSens sens''
                  case ps of
                    Result _ Nothing -> proveNodes l prover ln libEnv addTo
                    Result _ (Just pps) -> do
                      let provedOrDisproved allSentencesIncluded senStat =
                              P.isProvedStat senStat || allSentencesIncluded
                                   && case P.goalStatus senStat of
                                        P.Disproved -> True
                                        _ -> False
                          nwgoalMap = (markProved $ Comorphism
                                      $ IdComorphism lid1 $ top_sublogic lid1)
                                      lid1
                                      (filter (provedOrDisproved $ null
                                              $ OMap.keys thSens) pps) gMap
                          newTh = G_theory lid1 sig ind
                                    (Map.union thSens nwgoalMap) 0
                          (_,oldContents) =
                                      labNode' (safeContextDG
                                      "PGIP.Common.proveNodes"
                                      dGraph nb)
                          newNodeLab = oldContents{dgn_theory = newTh}
                          (nextDGraph,changes) =
                                      updateWithOneChange (SetNodeLab
                                      (error "proveNodes")
                                      (nb, newNodeLab)) dGraph []
                          rules = []
                          nextHistoryElem = (rules, changes)
                          result = mkResultProofStatus ln libEnv
                                         nextDGraph nextHistoryElem
                      proveNodes l prover ln result $
                                 GraphNode (nb, label) (Just newTh) : addTo

#endif
    _ : l -> proveNodes l prover ln libEnv addTo
    [] -> return (addTo,libEnv)

