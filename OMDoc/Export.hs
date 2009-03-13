{- |
Module      :  $Header$
Description :  export a development graph to an omdoc structure
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

A given development graph will be exported to an omdoc structure
which can then be output to XML via the XmlInterface.
-}

module OMDoc.Export
    ( exportDGraph
    , exportLabNode
    ) where

import Logic.Logic
import Logic.Prover

import Static.DevGraph
import Static.GTheory

import Common.ExtSign
import Common.Id
import Common.LibName

import OMDoc.DataTypes

import Data.Graph.Inductive.Graph
import Data.List
-- import Data.Maybe

-- | DGraph to OMDoc translation
exportDGraph :: LIB_NAME -> DGraph -> OMDoc
exportDGraph ln dg = OMDoc (show ln) $ map (exportLabNode ln dg) $
                     filter (not . isDGRef . snd) $ topsortedNodes dg

-- | DGNodeLab to TLTheory translation
exportLabNode :: LIB_NAME -> DGraph -> LNode DGNodeLab -> TLElement
exportLabNode ln dg (n, lb)
    | isDGRef lb =
        error "Ref nodes are not supported and should be filtered out before."
    | otherwise =
        let
            -- Filter the views from the imports:
            -- imports = innDG dg n
            libid = (getLIB_ID ln)
            specid = (mkSimpleId $ getDGNodeName lb)
        in case dgn_theory lb of
             G_theory lid (ExtSign sig _) _ sens _ ->
                 TLTheory (show $ specid)
               $ (export_signToOmdoc lid specid libid sig)
                     ++ (concatMap (export_senToOmdoc lid specid libid sig)
                        $ toNamedList sens)
