{- |
Module      :  $Header$
Description :  Navigation through the Development Graph
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  non-portable (via imports)

Navigation through the Development Graph based on Node and Link predicates
using Depth First Search.
-}

module Static.DGNavigation where

import Static.DevGraph

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List
import Data.Maybe

import Data.Graph.Inductive.Graph as Graph
import Logic.Grothendieck

-- * Navigator Class and Instance

linkSource :: LEdge a -> Node
linkLabel :: LEdge a -> a
linkSource (x,_,_) = x
linkLabel (_,_,x) = x

-- | The navigator instance consists of a 'LibEnv' a current 'DGraph' and
-- a current 'Node' which is the starting point for navigation through the DG.
newtype DGNav = DGNav (LibEnv, DGraph, Node)

class DevGraphNavigator a where
    -- | get all the incoming ledges of the current node
    directInn :: a -> [LEdge DGLinkLab]
    -- | get all the incoming ledges of the given node
    incoming :: a -> Node -> [LEdge DGLinkLab]
    -- | get the label of the given node
    getLabel :: a -> Node -> DGNodeLab
    -- | get the local (not referenced) label of the given node
    getLocalLabel :: a -> Node -> DGNodeLab
    getInLibEnv :: a -> (LibEnv -> DGraph -> b) -> b


instance DevGraphNavigator DGNav where
    directInn (DGNav (_, dg, n)) = innDG dg n
    incoming (DGNav (_, dg, _)) = innDG dg
    getLabel (DGNav (_, dg, _)) = labDG dg
    getLocalLabel (DGNav (le, dg, _)) n = snd $ lookupLocalNode le dg n
    getInLibEnv (DGNav (le, dg, _)) f = f le dg


-- TODO: these three functions can be moved to Static/DevGraph.hs

lookupLocalNodeByNameInEnv :: LibEnv -> String -> Maybe (LNode DGNodeLab)
lookupLocalNodeByNameInEnv le s = f $ Map.elems le where
    f [] = Nothing
    f (dg:l) = case lookupNodeByName s dg of
                 (nd, _):_ -> Just $ lookupLocalNode le dg nd
                 _ -> f l

lookupLocalNodeByName :: LibEnv -> DGraph -> String -> Maybe (LNode DGNodeLab)
lookupLocalNodeByName le dg s =
    case lookupNodeByName s dg of
      (nd, _):_ -> Just $ lookupLocalNode le dg nd
      _ -> Nothing

lookupLocalNode :: LibEnv -> DGraph -> Node -> LNode DGNodeLab
lookupLocalNode le = f
    where
      f dg n = case labDG dg n of
                 DGNodeLab { nodeInfo = DGRef { ref_libname = ln
                                              , ref_node = n' } } ->
                    f (lookupDGraph ln le) n'
                 x -> (n, x)


getLocalSyms :: DevGraphNavigator a => a -> Node -> Set.Set G_symbol
getLocalSyms dgnav n =
    case dgn_origin $ getLocalLabel dgnav n of
      DGBasicSpec _ s -> s
      _ -> Set.empty

-- * Basic search functionality

-- | DFS based search
firstMaybe :: (a -> Maybe b) -> [a] -> Maybe b
firstMaybe _ [] = Nothing
firstMaybe f (x:l) =
    case f x of
      Nothing -> firstMaybe f l
      y -> y

searchNode :: DevGraphNavigator a =>
                 (LNode DGNodeLab -> Bool) -> a -> Maybe (LNode DGNodeLab)
searchNode p dgnav =
    firstMaybe (searchNodeFrom p dgnav) $ map linkSource $ directInn dgnav

searchNodeFrom :: DevGraphNavigator a => (LNode DGNodeLab -> Bool) -> a
                  -> Node -> Maybe (LNode DGNodeLab)
searchNodeFrom p dgnav n =
    let ledgs = incoming dgnav n
        lbl = (n, getLabel dgnav n)
    in if p lbl then Just lbl
       else firstMaybe (searchNodeFrom p dgnav) $ map linkSource ledgs


searchLink :: DevGraphNavigator a =>
                 (LEdge DGLinkLab -> Bool) -> a -> Maybe (LEdge DGLinkLab)
searchLink p dgnav =
    firstMaybe (searchLinkFrom p dgnav) $ map linkSource $ directInn dgnav

searchLinkFrom :: DevGraphNavigator a => (LEdge DGLinkLab -> Bool) -> a
                  -> Node -> Maybe (LEdge DGLinkLab)
searchLinkFrom p dgnav n =
    let ledgs = incoming dgnav n
    in case find p ledgs of
         Nothing -> firstMaybe (searchLinkFrom p dgnav) $ map linkSource ledgs
         x -> x

-- * Predicates to be used with 'searchNode'

-- | This predicate is true for nodes with a nodename equal to the given string
dgnPredName :: String -> LNode DGNodeLab -> Maybe (LNode DGNodeLab)
dgnPredName n nd@(_, lbl) = if getDGNodeName lbl == n then Just nd else Nothing

-- | This predicate is true for nodes which are instantiations of a
-- specification with the given name
dgnPredParameterized :: String -> LNode DGNodeLab -> Maybe (LNode DGNodeLab)
dgnPredParameterized n nd@(_, DGNodeLab
                               { nodeInfo = DGNode { node_origin = DGInst sid }
                               })
    | show sid == n = Just nd
    | otherwise = Nothing
dgnPredParameterized _ _ = Nothing

-- * Predicates to be used with 'searchLink'
-- | This predicate is true for links which are argument instantiations of a
-- parameterized specification with the given name
dglPredActualParam :: String -> LEdge DGLinkLab -> Maybe (LEdge DGLinkLab)
dglPredActualParam n edg@(_, _, DGLink { dgl_origin = DGLinkInstArg sid })
    | show sid == n = Just edg
    | otherwise = Nothing
dglPredActualParam _ _ = Nothing

-- | This predicate is true for links which are instantiation morphisms
dglPredInstance :: LEdge DGLinkLab -> Maybe (LEdge DGLinkLab)
dglPredInstance edg@(_, _, DGLink { dgl_origin = DGLinkMorph _ }) = Just edg
dglPredInstance _ = Nothing

-- * Combined Node Queries

-- | Search for the given name in an actual parameter link
getActualParameterSpec :: DevGraphNavigator a => String -> a
                       -> Maybe (LNode DGNodeLab)
getActualParameterSpec n dgnav =
    -- search first actual param
    case searchLink (isJust . dglPredActualParam n) dgnav of
      Nothing -> Nothing
      Just (sn, _, _) ->
          -- get the spec for the param
          fmap f $ firstMaybe dglPredInstance $ incoming dgnav sn
              where f edg =
                        let sn' = linkSource edg in (sn', getLabel dgnav sn')

-- | Search for the given name in an instantiation node
getParameterizedSpec :: DevGraphNavigator a => String -> a
                     -> Maybe (LNode DGNodeLab)
getParameterizedSpec n dgnav =
    -- search first actual param
    case searchNode (isJust . dgnPredParameterized n) dgnav of
      Nothing -> Nothing
      Just (sn, _) ->
          -- get the spec for the param
          fmap f $ firstMaybe dglPredInstance $ incoming dgnav sn
              where f edg =
                        let sn' = linkSource edg in (sn', getLabel dgnav sn')

-- | Search for the given name in any node
getNamedSpec :: DevGraphNavigator a => String -> a -> Maybe (LNode DGNodeLab)
getNamedSpec n dgnav = searchNode (isJust . dgnPredName n) dgnav


-- | Combining a search function with an operation on nodes
fromSearchResult :: (DevGraphNavigator a) =>
                    (a -> Maybe (LNode DGNodeLab))
                        -> (a -> Node -> b) -> a -> Maybe b

fromSearchResult sf f dgnav = fmap (f dgnav . fst) $ sf dgnav
