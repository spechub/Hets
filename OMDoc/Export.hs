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

import Common.Result
import Common.ExtSign
import Common.Id
import Common.LibName

import OMDoc.DataTypes

import Data.Graph.Inductive.Graph
import Data.Maybe

-- | DGraph to OMDoc translation
exportDGraph :: LibName -> DGraph -> Result OMDoc
exportDGraph ln dg = do
  let libid = (getLibId ln)
  theories <- mapR (exportNodeLab libid dg) $ topsortedNodes dg
  views <- mapR (exportLinkLab libid dg) $ labEdgesDG dg
  return $ OMDoc (show ln) $ (catMaybes theories) ++ (catMaybes views)

-- | DGNodeLab to TLTheory translation
exportNodeLab :: LibId -> DGraph -> LNode DGNodeLab -> Result (Maybe TLElement)
exportNodeLab libid dg (n, lb) =
  if isDGRef lb then return Nothing else
      let specid = mkSimpleId $ getDGNodeName lb in
      case dgn_theory lb of
        G_theory lid (ExtSign sig _) _ sens _ ->
            do
              imports <- mapR (makeImport libid dg) $ innDG dg n
              return . Just . TLTheory (show specid) (omdoc_metatheory lid)
                         $ catMaybes imports
                         ++ export_signToOmdoc lid specid libid sig
                         ++ map (export_senToOmdoc lid specid libid sig)
                                (toNamedList sens)

makeImport :: LibId -> DGraph -> LEdge DGLinkLab -> Result (Maybe TCElement)
makeImport libid dg (from, _, lbl)
    | let lt = dgl_type lbl in isGlobalDef lt && (not $ isHidingEdge lt) =
          return . Just . TCImport (cdFromNode libid $ labDG dg from)
                   . makeMorphism libid $ dgl_morphism lbl
    | otherwise = return Nothing

-- | Given a TheoremLink we compute the view
exportLinkLab :: LibId -> DGraph -> LEdge DGLinkLab -> Result (Maybe TLElement)
exportLinkLab libid dg (from, to, lbl) = return $ case dgl_type lbl of
    ScopedLink Global (ThmLink _) _ ->
       Just . TLView (cdFromNode libid $ labDG dg from)
           (cdFromNode libid $ labDG dg to)
           . makeMorphism libid $ dgl_morphism lbl
    _ -> Nothing

makeMorphism :: LibId -> GMorphism -> TCElement
makeMorphism _ (GMorphism cid _ _ mor _) =
    export_morphismToOmdoc (targetLogic cid) mor

cdFromNode :: LibId -> DGNodeLab -> OMCD
cdFromNode libid lb =
-- special handling for library entries !??
    CD (getDGNodeName lb) $
    let omcdbase = show $ if isDGRef lb
                          then getLibId $ ref_libname $ nodeInfo lb
                          else libid
    in if omcdbase == "library" || omcdbase == ""
       then Nothing else Just omcdbase
