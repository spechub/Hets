{-| 
   
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

   Display of development graphs using dot
-}

module Static.DotGraph where

import Common.Lib.Graph
import Static.DevGraph
import Common.PrettyPrint

edgeAttribute :: DGLinkType -> String
edgeAttribute LocalDef = " [style=bold]"
edgeAttribute GlobalDef = " [style=bold]"
edgeAttribute HidingDef = " [style=bold]"
edgeAttribute (FreeDef _) = " [style=bold]"
edgeAttribute (CofreeDef _) = " [style=bold]"
edgeAttribute (LocalThm _ _ _)  = " [style=dotted]"
edgeAttribute (GlobalThm _ _ _) = " [style=dotted]"
edgeAttribute (HidingThm _ _) = " [style=dotted]"
edgeAttribute (FreeThm _ _) = " [style=dotted]"

showNode :: DGraph -> Node -> String
showNode dg n = 
  case get_dgn_name (lab' $ context n dg) of
    Nothing -> "N"++show n
    Just x -> showPretty x ""

dotEdge :: DGraph -> (Node, Node, DGLinkLab) -> String
dotEdge dg (n1,n2,link) = 
  showNode dg n1 ++ " -> " ++ showNode dg n2
	       ++ edgeAttribute (dgl_type link) ++ ";"
    
nodeAttribute :: DGNodeLab -> String
nodeAttribute (DGNode _ _ _ _) = ""
nodeAttribute (DGRef _ _ _) =  " [shape=box]"

dotNode :: DGraph -> (Node, DGNodeLab) -> String
dotNode dg (n,ncontents) =
  showNode dg n ++ nodeAttribute ncontents ++ ";"

dot :: DGraph -> [String]
dot dg =
  ["digraph G {","    size = \"8,6\"","  "] ++
  map (dotNode dg) (labNodes dg) ++ map (dotEdge dg) (labEdges dg)++["}"]
