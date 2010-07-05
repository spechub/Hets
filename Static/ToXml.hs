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
import Logic.Grothendieck

import Common.AS_Annotation
import Common.ConvertGlobalAnnos
import Common.DocUtils
import Common.ExtSign
import Common.GlobalAnnotations
import Common.Id
import Common.LibName
import qualified Common.OrderedMap as OMap
import Common.Result
import Common.ToXml

import Text.XML.Light

import Data.Graph.Inductive.Graph as Graph
import qualified Data.Map as Map
import qualified Data.Set as Set

dGraph :: LibEnv -> DGraph -> Element
dGraph lenv dg =
  let body = dgBody dg
      ga = globalAnnos dg
      lnodes = labNodes body
  in add_attr (mkAttr "nextlinkid" $ showEdgeId $ getNewEdgeId dg)
     $ unode "DGraph" $
         subnodes "Global" (annotations ga $ convertGlobalAnnos ga)
         ++ map (lnode ga lenv) lnodes
         ++ map (ledge ga dg) (labEdges body)
         ++ Map.foldWithKey (globalEntry ga dg) [] (globalEnv dg)

genSig :: DGraph -> GenSig -> [Attr]
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
    (unode "VIEW-DEFN" $ gmorph ga gm) : l
  _ -> l

gmorph :: GlobalAnnos -> GMorphism -> Element
gmorph ga gm@(GMorphism cid (ExtSign ssig _) _ tmor _) =
  case map_sign cid ssig of
    Result _ mr -> case mr of
      Nothing -> error $ "Static.ToXml.gmorph: " ++ showGlobalDoc ga gm ""
      Just (_, tsens) -> let
        tid = targetLogic cid
        sl = Map.toList . Map.filterWithKey (/=) $ symmap_of tid tmor
        psym = prettyElem "Symbol" ga
        in add_attr (mkNameAttr $ language_name cid)
           $ unode "GMorphism" $
             subnodes "Axioms" (map (mkAxNode ga) tsens)
             ++ map (\ (s, t) -> unode "map" [psym s, psym t]) sl

prettyRangeElem :: (GetRange a, Pretty a) => String -> GlobalAnnos -> a
                -> Element
prettyRangeElem s ga a =
  add_attrs (rangeAttrs $ getRangeSpan a) $ prettyElem s ga a

lnode :: GlobalAnnos -> LibEnv -> LNode DGNodeLab -> Element
lnode ga lenv (_, lbl) =
  let nm = dgn_name lbl
      (spn, xp) = case reverse $ xpath nm of
          ElemName s : t -> (s, showXPath t)
          l -> ("?", showXPath l)
  in add_attrs (mkNameAttr (showName nm) : if
               not (isDGRef lbl) && dgn_origin lbl < DGProof then
               [mkAttr "refname" spn, mkAttr "relxpath" xp ]
               else [])
  $ unode "DGNode"
    $ case nodeInfo lbl of
          DGRef li rf ->
            [ add_attrs [ mkAttr "library" $ show $ getLibId li
                        , mkAttr "node" $ getNameOfNode rf
                          $ lookupDGraph li lenv ]
            $ unode "Reference"
            $ prettyElem "Signature" ga $ dgn_sign lbl ]
          DGNode orig cs -> constStatus cs
              ++ case orig of
                   DGBasicSpec _ syms -> subnodes "Declarations"
                     (map (prettyRangeElem "Symbol" ga) $ Set.toList syms)
                   _ -> [prettyElem "Signature" ga $ dgn_sign lbl]
      ++ case dgn_theory lbl of
        G_theory lid (ExtSign sig _) _ thsens _ -> let
                 (axs, thms) = OMap.partition isAxiom $ OMap.map
                               (mapValue $ simplify_sen lid sig) thsens
                 in subnodes "Axioms"
                    (map (mkAxNode ga) $ toNamedList axs)
                    ++ subnodes "Theorems"
                    (map (mkThmNode ga) $ OMap.toList thms)

mkThmNode :: (GetRange s, Pretty s) => GlobalAnnos
          -> (String, SenStatus s (AnyComorphism, BasicProof)) -> Element
mkThmNode ga (n, th) = let s = sentence th in add_attrs
  (mkNameAttr n : mkProvenAttr (isProvenSenStatus th)
    : rangeAttrs (getRangeSpan s))
  $ prettyElem "Theorem" ga s

-- | a status may be open, proven or outdated
mkStatusAttr :: String -> Attr
mkStatusAttr = mkAttr "status"

mkProvenAttr :: Bool -> Attr
mkProvenAttr b = mkStatusAttr $ if b then "proven" else "open"

mkAxNode :: (GetRange s, Pretty s) => GlobalAnnos -> SenAttr s String -> Element
mkAxNode ga ax = let s = sentence ax in add_attrs
 (mkNameAttr (senAttr ax) : rangeAttrs (getRangeSpan s))
  $ prettyElem "Axiom" ga s

constStatus :: ConsStatus -> [Element]
constStatus cs = case show $ pretty cs of
  "" -> []
  cstr -> [unode "ConsStatus" cstr]

ledge :: GlobalAnnos -> DGraph -> LEdge DGLinkLab -> Element
ledge ga dg (f, t, lbl) = let
  typ = dgl_type lbl
  (lnkSt, stAttr) = case thmLinkStatus typ of
        Nothing -> ([], [])
        Just tls -> case tls of
          LeftOpen -> ([], [])
          Proven r ls -> (dgrule r ++
            map (\ e -> add_attr (mkAttr "linkref" $ showEdgeId e)
                   $ unode "ProofBasis" ()) (Set.toList $ proofBasis ls)
            , [unode "Status" "Proven"])
  in add_attrs
  [ mkAttr "source" $ getNameOfNode f dg
  , mkAttr "target" $ getNameOfNode t dg
  , mkAttr "linkid" $ showEdgeId $ dgl_id lbl ]
  $ unode "DGLink"
    $ unode "Type" (getDGLinkType lbl)
    : stAttr ++ lnkSt ++ constStatus (getLinkConsStatus typ)
    ++ [gmorph ga $ dgl_morphism lbl]

dgrule :: DGRule -> [Element]
dgrule r =
  unode "Rule" (dgRuleHeader r)
  : case r of
      DGRuleLocalInference m ->
        map (\ (s, t) -> add_attrs [mkNameAttr s, mkAttr "renamedTo" t]
             $ unode "MovedTheorems" ()) m
      Composition es -> map (\ (_, _, l) ->
        add_attr (mkAttr "linkref" $ showEdgeId $ dgl_id l)
        $ unode "RuleTarget" ()) es
      _ -> []
