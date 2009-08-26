{- |
Module      :  $Header$
Description :  xml output of Hets development graphs
Copyright   :  (c) Ewaryst Schulz, Uni Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

Xml of Hets DGs
-}

module Static.ToXml where

import Static.DevGraph
import Static.PrintDevGraph ()

import Common.DocUtils
import Common.GlobalAnnotations

import Text.XML.Light

import Data.Graph.Inductive.Graph as Graph
import qualified Data.Map as Map

mkAttr :: String -> String -> Attr
mkAttr = Attr . unqual

dGraph :: DGraph -> Element
dGraph dg =
  let body = dgBody dg
      ga = globalAnnos dg
      lnodes = labNodes body
      nm = Map.fromList $ map (\ (v, lbl) -> (v, dgn_name lbl)) lnodes
  in unode "DGraph" $ map (lnode ga) lnodes
         ++ map (ledge ga nm) (labEdges body)

lnode :: GlobalAnnos -> LNode DGNodeLab -> Element
lnode ga (_, lbl) =
  add_attr (mkAttr "name" . showName $ dgn_name lbl)
  $ unode "Node" $ showGlobalDoc ga lbl ""

lookupNodeName :: Int -> Map.Map Int NodeName -> String
lookupNodeName i = showName . Map.findWithDefault (error "lookupNodeName") i

ledge :: GlobalAnnos -> Map.Map Int NodeName -> LEdge DGLinkLab -> Element
ledge ga nm (f, t, lbl) =
  add_attrs [ mkAttr "source" $ lookupNodeName f nm
            , mkAttr "target" $ lookupNodeName t nm ]
  $ unode "Link" $ showGlobalDoc ga lbl ""

