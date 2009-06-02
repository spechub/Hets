{- |
Module      :  $Header$
Description :  export a development graph to an omega library
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

A given development graph will be exported to an omega library.
The structure of the development graph is expected to satisfy additional
requirements. The form of the specs should be the following:

spec <name> = spec-ref_1 and ... and spec-ref_n then basic-spec

n can also be 0 or 1.
-}

module Omega.Export
    ( exportDGraph
    , exportNodeLab
    ) where

--import Logic.Logic
--import Logic.Prover
--import Logic.Grothendieck
--import Logic.Comorphism

import Static.DevGraph
import Static.GTheory

import Common.ExtSign
import Common.Id
import Common.LibName

import Omega.DataTypes

import Data.Graph.Inductive.Graph
import Data.List
import Data.Maybe

-- | DGraph to Omega Library translation
exportDGraph :: LIB_NAME -> DGraph -> Library
exportDGraph ln dg =
    let libid = (getLIB_ID ln)
    in
      Library (show libid)
                  $ catMaybes $ map (exportNodeLab libid dg)
                  $ topsortedNodes dg

-- | DGNodeLab to String translation
exportNodeLab :: LIB_ID -> DGraph -> LNode DGNodeLab -> Maybe Theory
exportNodeLab libid dg (n, lb) =
    justWhen (not $ isDGRef lb) $
    let specid = mkSimpleId $ getDGNodeName lb
    in case dgn_theory lb of
         G_theory lid (ExtSign sig _) _ sens _ ->
             Theory (show specid)
                    (catMaybes (map (makeImport libid dg) $ innDG dg n))
                    []
                   
{-        ++ export_signToOmdoc lid specid libid sig
        ++ map (export_senToOmdoc lid specid libid sig) (toNamedList sens)
-}

makeImport :: LIB_ID -> DGraph -> LEdge DGLinkLab -> Maybe String
makeImport libid dg (from, _, lbl) =
  justWhen (isGlobalDef $ dgl_type lbl) $ getDGNodeName $ labDG dg from

