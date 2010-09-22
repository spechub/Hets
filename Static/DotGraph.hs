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
import Logic.Grothendieck (isHomogeneous)

edgeAttribute :: DGLinkType -> String
edgeAttribute l = case l of
  ScopedLink _ lk _ -> case lk of
    DefLink -> " ,style=bold"
    _ -> " ,arrowhead=onormal"
  HidingDefLink -> " ,style=bold, arrowhead=vee"
  FreeOrCofreeDefLink _ _ -> " ,style=bold"
  HidingFreeOrCofreeThm mh _ _ -> case mh of
    Nothing -> " ,arrowhead=vee"
    Just _ -> " ,arrowhead=onormal"

dotEdge :: LEdge DGLinkLab -> String
dotEdge (n1, n2, link) =
  show n1 ++ " -> " ++ show n2
               ++ " [id=" ++ showEdgeId (dgl_id link)
               ++ edgeAttribute (dgl_type link) ++ het
               ++ "];"
  where het = if isHomogeneous $ dgl_morphism link
                 then ""
                 else ", color=\"black:white:black\", arrowsize=1.6"

nodeAttribute :: Bool -> DGNodeLab -> String
nodeAttribute showInternal la =
   concatMap (", " ++) (inter la : ["shape=box" | isDGRef la]
                    ++ ["style=filled, fillcolor=grey" | hasOpenGoals la])
 where inter l = if isInternalNode l && not showInternal
                    then "label=\"\", height=0.2, width=0.35"
                    else "label=" ++ getDGNodeName la

dotNode :: Bool -> LNode DGNodeLab -> String
dotNode showInternal (n, ncontents) =
  show n ++ " [id=" ++ show n ++ nodeAttribute showInternal ncontents ++ "];"

-- | Generate a dot term representation out of a development graph
dotGraph :: FilePath
    -> Bool -- ^ True means show internal node labels
    -> DGraph -> String
dotGraph f showInternalNodeLabels dg = unlines $
  ["digraph " ++ show f ++ " {" ] ++
  map (dotNode showInternalNodeLabels) (labNodesDG dg) ++
  map dotEdge (labEdgesDG dg) ++ ["}"]
