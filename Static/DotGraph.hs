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

edgeAttributes :: DGEdgeType -> String
edgeAttributes ety = concatMap (", " ++)
  $ (if isInc ety then ["arrowsize=0.5"] else ["style=bold"])
  ++ case edgeTypeModInc ety of
    GlobalDef -> []
    HetDef -> ["color=" ++ doubleColor "black"]
    HidingDef -> ["color=blue"]
    LocalDef -> ["style=dashed"]
    FreeOrCofreeDef -> ["color=blue"]
    ThmType
      { thmEdgeType = thTy
      , isProvenEdge = isProv
      , isConservativ = isCons
      , isPending = isPend }
      -> let
      hc = ["color=" ++ if isPend then "cyan" else
             if isProv then "green" else "blue"]
      in case thTy of
      HidingThm -> "style=dashed" : hc
      FreeOrCofreeThm -> "style=dotted" : hc
      th -> let
        cl c = if isHomThm th then c else doubleColor c
        rc = if isProv then
               if isCons then
                 if isPend then "yellow" else show "/green"
               else "orange"
             else "red"
        in ("color=" ++ cl rc) : case isLocalThmType th of
        Global -> []
        Local -> ["style=dashed"]

doubleColor :: String -> String
doubleColor s = show $ s ++ ':' : s

dotEdge :: String -> LEdge DGLinkLab -> String
dotEdge url (n1, n2, link) = let
  cs = showConsStatus (getEdgeConsStatus link)
  es = showEdgeId (dgl_id link)
  in show n1 ++ " -> " ++ show n2
    ++ " [id=" ++ es
    ++ (if null url then "" else ", URL=" ++ show (url ++ "?edge=" ++ es))
    ++ (if null cs then "" else
        ", fontname=Helvetica, fontsize=10, label=" ++ show cs)
    ++ edgeAttributes (getRealDGLinkType link)
    ++ "];"

nodeAttribute :: Bool -> DGNodeLab -> String
nodeAttribute showInternal la = concatMap (", " ++)
  (inter la : ["shape=box" | isDGRef la]
   ++ [ "style=filled"
      , "fontsize=12"
      , "fontname=Helvetica"
      , "fillcolor=" ++ if hasOpenGoals la then "red" else
        if hasOpenNodeConsStatus False la then "yellow" else show "/green" ])
 where inter l = if isInternalNode l && not showInternal
                    then "label=\"\", height=0.1, width=0.2"
                    else "label=\"" ++ getDGNodeName la ++ "\""

dotNode :: Bool -> String -> LNode DGNodeLab -> String
dotNode showInternal url (n, ncontents) = let ns = show n in
  ns ++ " [id=" ++ ns
  ++ (if null url then "" else ", URL=" ++ show (url ++ "?node=" ++ ns))
  ++ nodeAttribute showInternal ncontents ++ "];"

-- | Generate a dot term representation out of a development graph
dotGraph :: FilePath
    -> Bool -- ^ True means show internal node labels
    -> String -- ^ URL for node and edge links
    -> DGraph -> String
dotGraph f showInternalNodeLabels url dg = unlines $
  ["digraph " ++ show f ++ " {" ]
  ++ map (dotNode showInternalNodeLabels url) (labNodesDG dg)
  ++ map (dotEdge url) (labEdgesDG dg)
  ++ ["}"]
