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
    , exportNodeLab
    ) where

import Logic.Logic
import Logic.Prover
import Logic.Grothendieck
import Logic.Comorphism

import Static.DevGraph
import Static.GTheory

import Common.ExtSign
import Common.Id
import Common.LibName

import OMDoc.DataTypes

import Data.Graph.Inductive.Graph
import Data.List
import Data.Maybe

-- | DGraph to OMDoc translation
exportDGraph :: LIB_NAME -> DGraph -> OMDoc
exportDGraph ln dg = let
      libid = (getLIB_ID ln)
    in OMDoc (show ln) $
           -- the theories
           (catMaybes $ map (exportNodeLab libid dg) $ topsortedNodes dg)
           ++
           -- the views
           (catMaybes $ map (exportLinkLab libid dg) $ labEdgesDG dg)

-- | DGNodeLab to TLTheory translation
exportNodeLab :: LIB_ID -> DGraph -> LNode DGNodeLab -> Maybe TLElement
exportNodeLab libid dg (n, lb) =
  if isDGRef lb then Nothing else
    let specid = mkSimpleId $ getDGNodeName lb
    in case dgn_theory lb of
    G_theory lid (ExtSign sig _) _ sens _ ->
      Just . TLTheory (show specid) (omdoc_metatheory lid)
        $ catMaybes (map (makeImport libid dg) $ innDG dg n)
        ++ export_signToOmdoc lid specid libid sig
        ++ map (export_senToOmdoc lid specid libid sig) (toNamedList sens)

makeImport :: LIB_ID -> DGraph -> LEdge DGLinkLab -> Maybe TCElement
makeImport libid dg (from, _, lbl) =
  if isGlobalDef $ dgl_type lbl then
  Just . TCImport (cdFromNode libid $ labDG dg from) . makeMorphism libid
  $ dgl_morphism lbl
  else Nothing

-- | Given a TheoremLink we compute the view
exportLinkLab :: LIB_ID -> DGraph -> LEdge DGLinkLab -> Maybe TLElement
exportLinkLab libid dg (from, to, lbl) = case dgl_type lbl of
    ScopedLink Global (ThmLink _) _ ->
       Just . TLView (cdFromNode libid $ labDG dg from)
           (cdFromNode libid $ labDG dg to)
           . makeMorphism libid $ dgl_morphism lbl
    _ -> Nothing

makeMorphism :: LIB_ID -> GMorphism -> TCElement
makeMorphism _ (GMorphism cid _ _ mor _) =
    export_morphismToOmdoc (targetLogic cid) mor

cdFromNode :: LIB_ID -> DGNodeLab -> OMCD
cdFromNode libid lb =
-- special handling for library entries !??
    CD (getDGNodeName lb) $
    let cdbase = show $ if isDGRef lb
                        then getLIB_ID $ ref_libname $ nodeInfo lb
                        else libid
    in if cdbase == "library" || cdbase == "" then Nothing else Just cdbase
