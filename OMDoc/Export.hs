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
exportNodeLab libid dg (n, lb)
    | isDGRef lb = Nothing
    | otherwise = Just $
      let
          specid = (mkSimpleId $ getDGNodeName lb)
      in case dgn_theory lb of
        G_theory lid (ExtSign sig _) _ sens _ ->
         TLTheory (show specid) $
          (catMaybes $ map (makeImport libid dg lb) $ (innDG dg n))
         ++ (export_signToOmdoc lid specid libid sig)
         ++ (map (export_senToOmdoc lid specid libid sig) $ toNamedList sens)


makeImport :: LIB_ID -> DGraph -> DGNodeLab -> LEdge DGLinkLab ->
               Maybe TCElement
makeImport libid dg nlb (from, _, (DGLink mor GlobalDef _ _)) = Just $
    let
        fromnode = labDG dg from
    in TCImport (cdFromNode libid fromnode) $ makeMorphism libid mor

makeImport _ _ _ _ = Nothing


-- | Given a TheoremLink we compute the view
exportLinkLab :: LIB_ID -> DGraph -> LEdge DGLinkLab -> Maybe TLElement
exportLinkLab libid dg (from, to, (DGLink mor (GlobalThm _ c _) _ _)) = Just $
    let
        fromnode = labDG dg from
        tonode = labDG dg to
    in TLView (cdFromNode libid fromnode)
           (cdFromNode libid tonode)
           $ makeMorphism libid mor

exportLinkLab _ _ _ = Nothing


makeMorphism :: LIB_ID -> GMorphism -> TCElement
makeMorphism _ (GMorphism cid _ _ mor _) =
    export_morphismToOmdoc (targetLogic cid) mor


cdFromNode :: LIB_ID -> DGNodeLab -> OMCD
cdFromNode libid lb =
    CD (getDGNodeName lb) $
    Just $ show $ if isDGRef lb
                  then getLIB_ID $ ref_libname $ nodeInfo lb
                  else libid



{-
data DGLinkLab = DGLink
  { dgl_morphism :: GMorphism  -- signature morphism of link
  , dgl_type :: DGLinkType     -- type: local, global, def, thm?
  , dgl_origin :: DGLinkOrigin -- origin in input language
  , dgl_id :: EdgeId          -- id of the edge
  } deriving (Show, Eq)


GMorphism
    { gMorphismComor :: cid
    , gMorphismSign :: ExtSign sign1 symbol1
    , gMorphismSignIdx :: SigId -- ^ 'G_sign' index of source signature
    , gMorphismMor :: morphism2
    , gMorphismMorIdx :: MorId  -- ^ `G_morphism index of target morphism
    } deriving Typeable
-}

