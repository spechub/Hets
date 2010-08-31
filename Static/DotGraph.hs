{- |
Module      :  $Header$
Description :  Display of development graphs using Graphviz\/dot
Copyright   :  (c) Till Mossakowski, Klaus Luettich Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Logic)

Display of development graphs using Graphviz\/dot
-}

module Static.DotGraph (dotGraph) where

import Data.Graph.Inductive.Graph
import Static.DevGraph
import Data.List (intercalate)
import Logic.Grothendieck (isHomogeneous)

edgeAttribute :: DGLinkType -> String
edgeAttribute l = case l of
  ScopedLink _ lk _ -> case lk of
    DefLink -> " [style=bold"
    _ -> " [arrowhead=onormal"
  HidingDefLink -> " [style=bold,arrowhead=vee"
  FreeOrCofreeDefLink _ _ -> " [style=bold"
  HidingFreeOrCofreeThm mh _ _ -> case mh of
    Nothing -> " [arrowhead=vee"
    Just _ -> " [arrowhead=onormal"

showNode :: DGraph -> Node -> String
showNode dg n = case getNameOfNode n dg of
                xs | null xs -> "n__" ++ show n
                   | otherwise -> xs

dotEdge :: DGraph -> LEdge DGLinkLab -> String
dotEdge dg (n1, n2, link) =
  showNode dg n1 ++ " -> " ++ showNode dg n2
               ++ edgeAttribute (dgl_type link) ++ het ++ "];"
  where het = if isHomogeneous $ dgl_morphism link
                 then ""
                 else ",color=\"black:white:black\",arrowsize=1.6"

nodeAttribute :: Bool -> DGNodeLab -> String
nodeAttribute showInternal la =
   case intercalate "," (inter la ++
                                  (if isDGRef la
                                      then ["shape=box"]
                                      else []) ++
                                  (if hasOpenGoals la
                                      then ["style=filled","fillcolor=grey"]
                                      else [])) of
   xs | null xs -> ""
      | otherwise -> '[' : xs ++ "]"
 where inter l = if isInternalNode l && not showInternal
                    then ["label=\"\",height=0.2,width=0.35"]
                    else []

dotNode :: Bool -> DGraph -> LNode DGNodeLab -> String
dotNode showInternal dg (n, ncontents) =
  showNode dg n ++ nodeAttribute showInternal ncontents ++ ";"

-- | Generate a dot term representation out of a development graph
dotGraph :: Bool -- ^ True means show internal node labels
    -> DGraph -> String
dotGraph showInternalNodeLabels dg = unlines $
  ["digraph G {","    size = \"8,6\"","  "] ++
  map (dotNode showInternalNodeLabels dg) (labNodesDG dg) ++
  map (dotEdge dg) (labEdgesDG dg)++["}"]
