{- |
Module      :$Header$
Description : utilitary functions used throughout the CMDL interface
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

PGIP.Utils contains different basic functions that are
used throughout the CMDL interface and could not be found in
Prelude

-}

module PGIP.DataTypesUtils
         ( getAllNodes
         , obtainGoalNodeList
         , getAllGoalNodes
         , getAllGoalEdges
         , getTh
         , baseChannels
         , genErrorMsg
         , genMessage
         , generatePrompter
         , add2hist
         , getIdComorphism
         ) where


import Interfaces.DataTypes
import Interfaces.Utils
import Interfaces.History
import PGIP.Utils
import PGIP.DataTypes
import Common.Result
import Data.List
import Data.Graph.Inductive.Graph
import Static.GTheory
import Static.DevGraph
import Proofs.TheoremHideShift
import System.IO

import Proofs.AbstractState
import Proofs.TheoremHideShift

import Static.GTheory
import Static.DevGraph

import Common.Result

import Data.Graph.Inductive.Graph
import Data.List


import Common.Result
import Logic.Comorphism
import Logic.Grothendieck


add2hist :: [UndoRedoElem] -> CMDL_State ->  CMDL_State
add2hist descr st
 = let intst = add2history [] (intState st)  descr
   in st {
         intState = intst }

-- | Given a list of selected theory generate an Id comorphism to the
-- first selected theory
getIdComorphism :: [Int_NodeInfo] -> Maybe AnyComorphism
getIdComorphism ls
 = case ls of
    [] -> Nothing
    (Element st _):_ ->
       case sublogicOfTheory st of
        (G_sublogics lid sub) -> Just $ Comorphism (mkIdComorphism lid sub)


-- | Generates the string containing the prompter
generatePrompter :: CMDL_State -> String
generatePrompter st
 = case i_state $ intState st of
    Nothing ->  prompterHead $ prompter st
    Just ist ->
     let pst = prompter st
         els = case elements ist of
                []  -> []
                el:[] -> case el of
                          Element sm _ ->"."++(theoryName sm)
                el:_ -> case el of
                          Element sm _ ->"." ++(theoryName sm)++ ".."
         cm = case elements ist of
               [] -> []
               _-> case cComorphism ist of
                    Nothing -> []
                    Just cm' ->
                     case getIdComorphism $ elements ist of
                      Nothing -> []
                      Just ocm ->
                        case cm' == ocm of
                          True -> []
                          False -> "*"
     in (delExtension $ fileLoaded pst) ++ els ++ cm ++ (prompterHead pst)


-- | Given a list of node names and the list of all nodes
-- the function returns all the nodes that have their name
-- in the name list but are also goals
obtainGoalNodeList :: CMDL_State -> [String] -> [LNode DGNodeLab]
                                 -> ([String],[LNode DGNodeLab])
obtainGoalNodeList state input ls
 = let (l1,l2) = obtainNodeList input ls
       l2' = filter (\(nb,nd) ->
                       let nwth = getTh Dont_translate nb state
                       in case nwth of
                           Nothing -> False
                           Just th -> nodeContainsGoals (nb,nd) th) l2
   in (l1,l2')


-- | Returns the list of all nodes that are goals,
-- taking care of the up to date status
getAllGoalNodes :: CMDL_State ->  [LNode DGNodeLab]
getAllGoalNodes st
 = case i_state $ intState st of
    Nothing -> []
    Just ist ->
      filter (\(nb,nd) ->
             let nwth = getTh Dont_translate nb st
             in case nwth of
                 Nothing -> False
                 Just th -> nodeContainsGoals (nb,nd) th) $
                                 getAllNodes $ ist

-- | Returns the list of all goal edges taking care of the
-- up to date status
getAllGoalEdges :: CMDL_State -> [LEdge DGLinkLab]
getAllGoalEdges st
 = case i_state $ intState st of
    Nothing -> []
    Just ist ->
      filter edgeContainsGoals $ getAllEdges $ ist


--local function that computes the theory of a node
--that takes into consideration translated theories in
--the selection too and returns the theory as a string
getTh :: CMDL_UseTranslation -> Int -> CMDL_State -> Maybe G_theory
getTh useTrans x st
 = let
    -- compute the theory for a given node
       fn n = case i_state $ intState st of
               Nothing -> Nothing
               Just ist -> maybeResult $
                 computeTheory (i_libEnv ist) (i_ln ist) n
   in
    case useTrans of
     Dont_translate -> fn x
     Do_translate ->
      case i_state $ intState st of
       Nothing -> Nothing
       Just ist ->
        case elements ist of
         [] -> fn x
         _ ->
          case find (\y -> case y of
                          Element _ z -> z == x) $
                  elements ist of
           Nothing -> fn x
           Just _ ->
            case cComorphism ist of
             Nothing -> fn x
             Just cm ->
              case fn x of
               Nothing -> Nothing
               Just sth->
                case mapG_theory cm sth of
                  Result _ Nothing -> Just sth
                  Result _ (Just sth') -> Just sth'


-- | Generates the base channels to be used (stdin and stdout)
baseChannels :: [CMDL_Channel]
baseChannels
 = let ch_in  = CMDL_Channel {
                  chName       = "stdin",
                  chType       = ChStdin,
                  chHandler    = stdin,
                  chSocket     = Nothing,
                  chProperties = ChRead
                  }
       ch_out = CMDL_Channel {
                  chName       = "stdout",
                  chType       = ChStdout,
                  chHandler    = stdout,
                  chSocket     = Nothing,
                  chProperties = ChWrite
                  }
   in ch_in : ch_out : []


genErrorMsg :: String -> CMDL_State -> CMDL_State
genErrorMsg msg st
 = st {
      output = CMDL_Message {
         outputMsg = [],
         warningMsg = [],
         errorMsg = msg
         }
     }

genMessage :: String -> String -> CMDL_State -> CMDL_State
genMessage warnings msg st
 = st{
      output = CMDL_Message {
        outputMsg = msg,
        warningMsg = warnings,
        errorMsg = []
        }
     }

