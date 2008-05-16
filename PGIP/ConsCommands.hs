{- |
Module      :$Header$
Description : CMDL interface commands
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

PGIP.ConsCommands contains all commands
related to consistency\/conservativity checks
-}

module PGIP.ConsCommands
       ( cConsChecker
       , cConservCheck
       , cConservCheckAll
       , cConsistCheck
       , cConsistCheckAll
       ) where

import PGIP.DataTypes
import PGIP.Utils
import PGIP.DataTypesUtils
import Static.DevGraph
import Data.Graph.Inductive.Graph
import Data.List
import Data.Char


cConsChecker:: String -> CMDL_State -> IO CMDL_State
cConsChecker _ state=
	return state

cConservCheck:: String -> CMDL_State -> IO CMDL_State
cConservCheck input state = 
  case devGraphState state of 
   Nothing ->
     return $ genErrorMsg "No library loaded" state
   Just dgState -> do
     let (_,edg,nbEdg,errs) = decomposeIntoGoals input
         tmpErrs = prettyPrintErrList errs
     case (edg,nbEdg) of 
      ([],[]) ->
        return $genErrorMsg( tmpErrs++"No edges in input string\n") state
      (_,_) ->
        do 
         let lsNodes = getAllNodes dgState
             lsEdges = getAllEdges dgState
             allList = conservativityList lsNodes lsEdges
             edgLs = concatMap (\x -> case find (
                                        \(s1,_) -> s1 == x) allList of 
                                       Nothing -> []
                                       Just (s1,s2) -> [(s1,s2)]) edg
             nbEdgLs = concatMap (\x -> case find (
                                        \(s1,_) -> s1 == x) allList of
                                       Nothing -> []
                                       Just (s1,s2) -> [(s1,s2)]) nbEdg
         case edgLs++nbEdgLs of
          [] -> return $ genErrorMsg (tmpErrs ++ "No edge in input string\n")
                                                             state
          _ ->
           do
              return $ genMessage tmpErrs
                         (concatMap (\(s1,s2) -> s1++" : "++s2++"\n") 
                                       (edgLs ++ nbEdgLs) ) state




cConservCheckAll :: CMDL_State -> IO CMDL_State
cConservCheckAll state =
   case devGraphState state of 
    Nothing ->
              return $ genErrorMsg "No library loaded" state
    Just dgState ->
     do
      return $ genMessage [] 
                (concatMap (\(s1,s2) -> s1++" : "++s2++"\n") $
                 conservativityList (getAllNodes dgState) 
                                    (getAllEdges dgState)) state


cConsistCheck :: String -> CMDL_State -> IO CMDL_State
cConsistCheck _ state = 
	return state

cConsistCheckAll :: CMDL_State -> IO CMDL_State
cConsistCheckAll state =
	return state

{- | returns the conservativity of the given edge -}
getConservativity :: LEdge DGLinkLab -> Conservativity
getConservativity (_,_,labl) =
  case dgl_type labl of
    LocalThm _ cons _ -> cons
    GlobalThm _ cons _ -> cons
    _ -> maximum [ None ,Cons, Mono, Def ]

getConservativityName :: LEdge DGLinkLab -> String
getConservativityName edgl =
  case getConservativity edgl of 
    None -> "Inconsistent"
    Cons -> "Conservativity"
    Mono -> "Monomorphic"
    Def  -> "Definitional"

conservativityList:: [LNode DGNodeLab] -> 
                     [LEdge DGLinkLab] -> [(String,String)]
conservativityList lsN lsE
 =
  let
  -- function that returns the name of a node given its number
   nameOf x ls = case find(\(nb,_) -> nb == x) ls of
                  Nothing -> "Unknown node"
                  Just (_, nlab) -> showName $ dgn_name nlab
   ordFn x y = let (x1,x2,_) = x
                   (y1,y2,_) = y
               in if (x1,x2) > (y1,y2) then GT
                   else if (x1,x2) < (y1,y2) then LT
                         else EQ
  -- sorted and grouped list of edges
   edgs = groupBy ( \(x1,x2,_) (y1,y2,_)-> (x1,x2)==(y1,y2)) $
           sortBy ordFn lsE
   allEds= concatMap (\l -> case l of
                             [(x,y,edgLab)]->[((nameOf x lsN) ++ " -> " ++
                                      (nameOf y lsN) ,
                                      getConservativityName (x,y,edgLab))]
                             _ -> map (\(x,y,edgLab) ->
                                            (((nameOf x lsN) ++ " -> " ++
                                             (show $ dgl_id edgLab) ++ 
                                             " -> " ++
                                             (nameOf y lsN)),
                                             (getConservativityName 
                                                  (x,y,edgLab))))
                                                             l) edgs
  in allEds



