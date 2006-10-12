{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Klaus Lüttich Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

Display of development graphs using Graphviz\/dot
-}

module Static.DotGraph(dotGraph) where

import Data.Graph.Inductive.Graph
import Static.DevGraph
import Data.List (intersperse)
import Logic.Grothendieck (isHomogeneous)

edgeAttribute :: DGLinkType -> String
edgeAttribute LocalDef = " [style=bold"
edgeAttribute GlobalDef = " [style=bold"
edgeAttribute HidingDef = " [style=bold,arrowhead=vee"
edgeAttribute (FreeDef _) = " [style=bold"
edgeAttribute (CofreeDef _) = " [style=bold"
edgeAttribute (LocalThm _ _con _)  = " [arrowhead=onormal" 
edgeAttribute (GlobalThm _ _con _) = " [arrowhead=onormal" 
edgeAttribute (HidingThm _ _) = " [arrowhead=vee"
edgeAttribute (FreeThm _ _) = " [arrowhead=onormal"

showNode :: DGraph -> Node -> String
showNode dg n = case getDGNodeName $ lab' $ context dg n of
                xs | null xs -> "n__" ++ show n
                   | otherwise -> xs

dotEdge :: DGraph -> (Node, Node, DGLinkLab) -> String
dotEdge dg (n1, n2, link) =
  showNode dg n1 ++ " -> " ++ showNode dg n2
               ++ edgeAttribute (dgl_type link) ++ het ++ "];"
  where het = if isHomogeneous $ dgl_morphism link 
                 then "" 
                 else ",color=\"black:white:black\",arrowsize=1.6"

nodeAttribute :: Bool -> DGNodeLab -> String
nodeAttribute showInternal la =
   case concat $ intersperse "," (inter la ++
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

dotNode :: Bool -> DGraph -> (Node, DGNodeLab) -> String
dotNode showInternal dg (n, ncontents) =
  showNode dg n ++ nodeAttribute showInternal ncontents ++ ";"

-- | Generate a dot term representation out of a development graph
dotGraph :: Bool -- ^ True means show internal node labels
    -> DGraph -> String
dotGraph showInternalNodeLabels dg = unlines $
  ["digraph G {","    size = \"8,6\"","  "] ++
  map (dotNode showInternalNodeLabels dg) (labNodes dg) ++
  map (dotEdge dg) (labEdges dg)++["}"]
