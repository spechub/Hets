{- |
Module      :  ./Static/DGNavigation.hs
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

import qualified Data.Set as Set
import Data.List
import Data.Maybe

import Data.Graph.Inductive.Graph as Graph
import Logic.Grothendieck

import Common.Doc
import Common.DocUtils
import Syntax.AS_Library

-- * Navigator Class

class DevGraphNavigator a where
    -- | get all the incoming ledges of the given node
    incoming :: a -> Node -> [LEdge DGLinkLab]
    -- | get the label of the given node
    getLabel :: a -> Node -> DGNodeLab
    -- | get the local (not referenced) environment of the given node
    getLocalNode :: a -> Node -> (DGraph, LNode DGNodeLab)
    getInLibEnv :: a -> (LibEnv -> DGraph -> b) -> b
    getCurrent :: a -> [LNode DGNodeLab]
    relocate :: a -> DGraph -> [LNode DGNodeLab] -> a


{- | Get all the incoming ledges of the given node and eventually
cross the border to an other 'DGraph'. The new 'DevGraphNavigator'
is returned with 'DGraph' set to the new graph and current node to
the given node. -}
followIncoming :: DevGraphNavigator a => a -> Node
                    -> (a, LNode DGNodeLab, [LEdge DGLinkLab])
followIncoming dgn n = (dgn', lbln, incoming dgn' n')
    where (dgn', lbln@(n', _)) = followNode dgn n

-- | get the local (not referenced) label of the given node
getLocalLabel :: DevGraphNavigator a => a -> Node -> DGNodeLab
getLocalLabel dgnav = snd . snd . getLocalNode dgnav

followNode :: DevGraphNavigator a => a -> Node -> (a, LNode DGNodeLab)
followNode dgnav n = (relocate dgnav dg [lbln], lbln)
    where (dg, lbln) = getLocalNode dgnav n

-- | get all the incoming ledges of the current node
directInn :: DevGraphNavigator a => a -> [LEdge DGLinkLab]
directInn dgnav = concatMap (incoming dgnav . fst) $ getCurrent dgnav


-- * Navigator Instance

{- | The navigator instance consists of a 'LibEnv' a current 'DGraph' and
a current 'Node' which is the starting point for navigation through the DG. -}
data DGNav = DGNav { dgnLibEnv :: LibEnv
                   , dgnDG :: DGraph
                   , dgnCurrent :: [LNode DGNodeLab] } deriving Show


instance Pretty DGNav where
    pretty dgn = d1 <> text ":" <+> pretty (map fst $ dgnCurrent dgn)
                      where d1 = case optLibDefn $ dgnDG dgn of
                                   Just (Lib_defn ln _ _ _) -> pretty ln
                                   Nothing -> text "DG"

makeDGNav :: LibEnv -> DGraph -> [LNode DGNodeLab] -> DGNav
makeDGNav le dg cnl = DGNav le dg cnl' where
    cnl' | null cnl = filter f $ labNodesDG dg
         | otherwise = cnl
         where f (n, _) = not $ any isDefLink $ outDG dg n

isDefLink :: LEdge DGLinkLab -> Bool
isDefLink = isDefEdge . dgl_type . linkLabel

instance DevGraphNavigator DGNav where
    -- we consider only the definition links in a DGraph
    incoming dgn = filter isDefLink . innDG (dgnDG dgn)
    getLabel = labDG . dgnDG
    getLocalNode (DGNav {dgnLibEnv = le, dgnDG = dg}) = lookupLocalNode le dg
    getInLibEnv (DGNav {dgnLibEnv = le, dgnDG = dg}) f = f le dg
    getCurrent (DGNav {dgnCurrent = lblnl}) = lblnl
    relocate dgn dg lblnl = dgn { dgnDG = dg, dgnCurrent = lblnl }


-- * Basic search functionality

-- | DFS based search
firstMaybe :: (a -> Maybe b) -> [a] -> Maybe b
firstMaybe _ [] = Nothing
firstMaybe f (x : l) =
    case f x of
      Nothing -> firstMaybe f l
      y -> y

{- | Searches all ancestor nodes of the current node and also the current node
for a node matching the given predicate -}
searchNode :: DevGraphNavigator a =>
                 (LNode DGNodeLab -> Bool) -> a -> Maybe (a, LNode DGNodeLab)
searchNode p dgnav =
    firstMaybe (searchNodeFrom p dgnav . fst) $ getCurrent dgnav

searchNodeFrom :: DevGraphNavigator a => (LNode DGNodeLab -> Bool) -> a
               -> Node -> Maybe (a, LNode DGNodeLab)
searchNodeFrom p dgnav n =
    let (dgnav', lbln, ledgs) = followIncoming dgnav n
    in if p lbln then Just (dgnav', lbln)
       else firstMaybe (searchNodeFrom p dgnav') $ map linkSource ledgs


searchLink :: DevGraphNavigator a =>
                 (LEdge DGLinkLab -> Bool) -> a -> Maybe (a, LEdge DGLinkLab)
searchLink p dgnav =
    firstMaybe (searchLinkFrom p dgnav . fst) $ getCurrent dgnav

searchLinkFrom :: DevGraphNavigator a => (LEdge DGLinkLab -> Bool) -> a
                  -> Node -> Maybe (a, LEdge DGLinkLab)
searchLinkFrom p dgnav n =
    let (dgnav', _, ledgs) = followIncoming dgnav n
    in case find p ledgs of
         Nothing -> firstMaybe (searchLinkFrom p dgnav') $ map linkSource ledgs
         x -> fmap ((,) dgnav') x

-- * Predicates to be used with 'searchNode'

-- | This predicate is true for nodes with a nodename equal to the given string
dgnPredName :: String -> LNode DGNodeLab -> Maybe (LNode DGNodeLab)
dgnPredName n nd@(_, lbl) = if getDGNodeName lbl == n then Just nd else Nothing

{- | This predicate is true for nodes which are instantiations of a
specification with the given name -}
dgnPredParameterized :: String -> LNode DGNodeLab -> Maybe (LNode DGNodeLab)
dgnPredParameterized n nd@(_, DGNodeLab
                               { nodeInfo = DGNode { node_origin = DGInst sid }
                               })
    | show sid == n = Just nd
    | otherwise = Nothing
dgnPredParameterized _ _ = Nothing

{- * Predicates to be used with 'searchLink'
This predicate is true for links which are argument instantiations of a
parameterized specification with the given name -}
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
                       -> Maybe (a, LNode DGNodeLab)
getActualParameterSpec n dgnav =
    -- search first actual param
    case searchLink (isJust . dglPredActualParam n) dgnav of
      Nothing -> Nothing
      Just (dgn', (sn, _, _)) ->
          -- get the spec for the param
          fmap f $ firstMaybe dglPredInstance $ incoming dgnav sn
              where f edg = let sn' = linkSource edg
                            in (dgn', (sn', getLabel dgnav sn'))


-- | Search for the given name in an instantiation node
getParameterizedSpec :: DevGraphNavigator a => String -> a
                     -> Maybe (a, LNode DGNodeLab)
getParameterizedSpec n dgnav =
    -- search first actual param
    case searchNode (isJust . dgnPredParameterized n) dgnav of
      Nothing -> Nothing
      Just (dgn', (sn, _)) ->
          -- get the spec for the param
          fmap f $ firstMaybe dglPredInstance $ incoming dgnav sn
              where f edg = let sn' = linkSource edg
                            in (dgn', (sn', getLabel dgnav sn'))

-- | Search for the given name in any node
getNamedSpec :: DevGraphNavigator a => String -> a -> Maybe (a, LNode DGNodeLab)
getNamedSpec n = searchNode (isJust . dgnPredName n)


-- | Combining a search function with an operation on nodes
fromSearchResult :: (DevGraphNavigator a) =>
                    (a -> Maybe (a, LNode DGNodeLab))
                        -> (a -> Node -> b) -> a -> Maybe b
fromSearchResult sf f dgnav = case sf dgnav of
                                Just (dgn', (n, _)) -> Just $ f dgn' n
                                _ -> Nothing

-- * Other utils

getLocalSyms :: DevGraphNavigator a => a -> Node -> Set.Set G_symbol
getLocalSyms dgnav n =
    case dgn_origin $ getLocalLabel dgnav n of
      DGBasicSpec _ _ s -> s
      _ -> Set.empty

linkSource :: LEdge a -> Node
linkLabel :: LEdge a -> a
linkSource (x, _, _) = x
linkLabel (_, _, x) = x
