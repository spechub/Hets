{- HetCATS/Static/DotGraph.hs
   $Id$
   Till Mossakowski

   Display of development graphs using dot
-}

module Static.DotGraph where

import Common.Lib.Graph
import Static.DevGraph
import Syntax.Print_HetCASL


edgeAttribute LocalDef = " [style=bold]"
edgeAttribute GlobalDef = " [style=bold]"
edgeAttribute HidingDef = " [style=bold]"
edgeAttribute (FreeDef _) = " [style=bold]"
edgeAttribute (CofreeDef _) = " [style=bold]"
edgeAttribute (LocalThm _ _)  = " [style=dotted]"
edgeAttribute (GlobalThm _ _) = " [style=dotted]"
edgeAttribute (HidingThm _ _) = " [style=dotted]"
edgeAttribute (FreeThm _ _) = " [style=dotted]"

showNode :: DGraph -> Node -> String
showNode dg n = 
  case get_dgn_name (lab' $ context n dg) of
    Nothing -> "N"++show n
    Just x -> show (printText0_eGA x)

dotEdge dg (n1,n2,link) = 
  showNode dg n1 ++ " -> " ++ showNode dg n2++ edgeAttribute (dgl_type link) ++ ";"
    
nodeAttribute (DGNode _ _ _ _) = ""
nodeAttribute (DGRef _ _ _) =  " [shape=box]"

dotNode dg (n,ncontents) =
  showNode dg n ++ nodeAttribute ncontents ++ ";"

dot :: DGraph -> [String]
dot dg =
  ["digraph G {","    size = \"8,6\"","  "] ++
  map (dotNode dg) (labNodes dg) ++ map (dotEdge dg) (labEdges dg)++["}"]
