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
             (errs',listEdges) = obtainEdgeList edg nbEdg lsNodes lsEdges
             tmpErrs' = tmpErrs ++ (prettyPrintErrList errs')
         case listEdges of
          [] -> return $ genErrorMsg (tmpErrs' ++ "No edge in input string\n")
                                                             state
          _ ->
           do
            case getConservativityOfPath listEdges of
             None -> return $ genMessage tmpErrs' 
                                     "Conservativity found: None" state
             Cons -> return $ genMessage tmpErrs'
                                     "Conservativity found: Cons" state
             Mono -> return $ genMessage tmpErrs'
                                     "Conservativity found: Mono" state
             Def -> return $ genMessage tmpErrs'
                                     "Conservativity found: Def" state




cConservCheckAll :: CMDL_State -> IO CMDL_State
cConservCheckAll state =
   case devGraphState state of 
    Nothing ->
              return $ genErrorMsg "No library loaded" state
    Just dgState ->
     do
      case getConservativityOfPath $ getAllEdges dgState of
        None -> return $ genMessage [] 
                                "Conservativity found: None" state
        Cons -> return $ genMessage []
                                "Conservativity found: Cons" state
        Mono -> return $ genMessage []
                                "Conservativity found: Mono" state
        Def -> return $ genMessage []
                                "Conservativity found: Def" state


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

{- | returns the conservativity of the given path -}
getConservativityOfPath :: [LEdge DGLinkLab] -> Conservativity
getConservativityOfPath path = minimum [getConservativity e | e <- path]


