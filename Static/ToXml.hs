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
import Static.GTheory
import Static.PrintDevGraph

import Logic.Prover
import Logic.Logic
import Logic.Comorphism

import Common.AS_Annotation
import Common.ConvertGlobalAnnos
import Common.DocUtils
import Common.ExtSign
import Common.GlobalAnnotations
import Common.Id
import Common.LibName
import qualified Common.OrderedMap as OMap
import Common.ToXml

import Text.XML.Light

import Data.Graph.Inductive.Graph as Graph
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List

dGraph :: LibEnv -> DGraph -> Element
dGraph lenv dg =
  let body = dgBody dg
      ga = globalAnnos dg
      lnodes = labNodes body
  in unode "DGraph" $
         subnodes "Global" (annotations ga $ convertGlobalAnnos ga)
         ++ map (lnode ga lenv) lnodes
         ++ map (ledge ga dg) (labEdges body)
         ++ Map.foldWithKey (globalEntry ga dg) [] (globalEnv dg)

genSig :: DGraph  -> GenSig -> [Attr]
genSig dg (GenSig _ _ allparams) = case allparams of
   EmptyNode _ -> []
   JustNode (NodeSig n _) -> [mkAttr "formal-param" $ getNameOfNode n dg]

globalEntry :: GlobalAnnos -> DGraph -> SIMPLE_ID -> GlobalEntry
            -> [Element] -> [Element]
globalEntry ga dg si ge l = case ge of
  SpecEntry (ExtGenSig g (NodeSig n _)) ->
    add_attrs (mkNameAttr (getNameOfNode n dg) :
      rangeAttrs (getRangeSpan si) ++ genSig dg g)
    (unode "SPEC-DEFN" ()) : l
  ViewEntry (ExtViewSig (NodeSig s _) gm (ExtGenSig g (NodeSig n _))) ->
    add_attrs (mkNameAttr (show si) : rangeAttrs (getRangeSpan si)
      ++ genSig dg g ++
      [ mkAttr "source" $ getNameOfNode s dg
      , mkAttr "target" $ getNameOfNode n dg])
    (unode "VIEW-DEFN" $ prettyElem "GMorphism" ga gm) : l
  _ -> l

lnode :: GlobalAnnos -> LibEnv -> LNode DGNodeLab -> Element
lnode ga lenv (_, lbl) =
  let nm = dgn_name lbl
      (spn, xp) = case reverse $ xpath nm of
          ElemName s : t -> (s, showXPath t)
          l -> ("?", showXPath l)
  in add_attrs (mkNameAttr (showName nm) : if
               dgn_origin lbl < DGProof then
               [mkAttr "specname" spn, mkAttr "relxpath" xp ]
               else [])
  $ unode "Node"
    $ case nodeInfo lbl of
          DGRef li rf ->
            [ add_attrs [ mkAttr "library" $ show $ getLIB_ID li
                        , mkAttr "node" $ getNameOfNode rf
                          $ lookupDGraph li lenv ]
            $ unode "Reference"
            $ prettyElem "Signature" ga $ dgn_sign lbl ]
          DGNode orig cs ->
              (case dgOriginSpec orig of
                  Nothing -> []
                  Just si -> [unode "OriginSpec" $ tokStr si])
              ++ (case show $ pretty cs of
                   "" -> []
                   cstr -> [unode "ConsStatus" cstr])
              ++ case orig of
                   DGBasicSpec syms -> subnodes "Declarations"
                     (map (prettyElem "Symbol" ga) $ Set.toList syms)
                   _ -> []
      ++ case dgn_theory lbl of
        G_theory lid (ExtSign sig _) _ thsens _ -> let
                 (axs, thms) = OMap.partition isAxiom $ OMap.map
                               (mapValue $ simplify_sen lid sig) thsens
                 in subnodes "Axioms"
                    (map (mkAxNode ga) $ toNamedList axs)
                    ++ subnodes "Theorems"
                    (map (mkThmNode ga) $ OMap.toList thms)

mkThmNode :: Pretty s => GlobalAnnos
          -> (String, SenStatus s (AnyComorphism, BasicProof)) -> Element
mkThmNode ga (n, s) = add_attrs
  [ mkNameAttr n
  , mkAttr "status" $ if isProvenSenStatus s then "proven" else "open" ]
  $ prettyElem "Theorem" ga $ sentence s

mkAxNode :: Pretty s => GlobalAnnos -> SenAttr s String -> Element
mkAxNode ga s = add_attr (mkNameAttr $ senAttr s)
  $ prettyElem "Axiom" ga $ sentence s

ledge :: GlobalAnnos -> DGraph -> LEdge DGLinkLab -> Element
ledge ga dg (f, t, lbl) = let orig = dgl_origin lbl in
  add_attrs [ mkAttr "source" $ getNameOfNode f dg
            , mkAttr "target" $ getNameOfNode t dg ]
  $ unode "Link"
    $ unode "Origin" (dgLinkOriginHeader orig)
      : case dgLinkOriginSpec orig of
          Nothing -> []
          Just si -> [unode "OriginSpec" $ tokStr si]
      ++ [ prettyElem "Type" ga $ dgl_type lbl
         , prettyElem "GMorphism" ga $ dgl_morphism lbl ]
