{- |
Module      :  $Header$
Description :  xml output of Hets development graphs
Copyright   :  (c) Ewaryst Schulz, Uni Bremen 2009
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

Xml of Hets DGs
-}

module Static.ToXml (dGraph, lnode, showSymbols, showSymbolsTh) where

import Static.DgUtils
import Static.DevGraph
import Static.GTheory
import Static.PrintDevGraph

import Logic.Prover
import Logic.Logic
import Logic.Comorphism
import Logic.Grothendieck

import Common.AS_Annotation
import Common.ConvertGlobalAnnos
import Common.Consistency
import Common.Doc
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
import qualified Data.Set as Set (toList)

dGraph :: LibEnv -> LibName -> DGraph -> Element
dGraph lenv ln dg =
  let body = dgBody dg
      ga = globalAnnos dg
      lnodes = labNodes body
  in add_attrs [ mkAttr "filename" $ getFilePath ln
               , mkAttr "libname" $ show $ getLibId ln
               , mkAttr "nextlinkid" $ showEdgeId $ getNewEdgeId dg ]
     $ unode "DGraph" $
         subnodes "Global" (annotations ga $ convertGlobalAnnos ga)
         ++ map (lnode ga lenv) lnodes
         ++ map (ledge ga dg) (labEdges body)

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
             subnodes "Axioms"
             (map (mkAxDocNode ga . print_named (targetLogic cid)) tsens)
             ++ map (\ (s, t) -> unode "map" [psym s, psym t]) sl

prettyRangeElem :: (GetRange a, Pretty a) => String -> GlobalAnnos -> a
                -> Element
prettyRangeElem s ga a =
  add_attrs (rangeAttrs $ getRangeSpan a) $ prettyElem s ga a

prettySymbol :: (GetRange a, Pretty a) => GlobalAnnos -> a -> Element
prettySymbol = prettyRangeElem "Symbol"

lnode :: GlobalAnnos -> LibEnv -> LNode DGNodeLab -> Element
lnode ga lenv (_, lbl) =
  let nm = dgn_name lbl
      (spn, xp) = case reverse $ xpath nm of
          ElemName s : t -> (s, showXPath t)
          l -> ("?", showXPath l)
  in add_attrs (mkNameAttr (showName nm)
    : if not (isDGRef lbl) then case signOf $ dgn_theory lbl of
        G_sign slid _ _ -> mkAttr "logic" (show slid)
          : if dgn_origin lbl < DGProof then
             [mkAttr "refname" spn, mkAttr "relxpath" xp ]
          else [] else [])
  $ unode "DGNode"
    $ case nodeInfo lbl of
          DGRef li rf ->
            [ add_attrs [ mkAttr "library" $ show $ getLibId li
                        , mkAttr "node" $ getNameOfNode rf
                          $ lookupDGraph li lenv ]
            $ unode "Reference" () ]
          DGNode orig cs -> consStatus cs ++ case orig of
                   DGBasicSpec _ (G_sign lid (ExtSign dsig _) _) _ ->
                     subnodes "Declarations"
                       $ map (prettySymbol ga)
                       $ mostSymsOf lid dsig
                   DGRestriction _ hidSyms -> subnodes "Hidden"
                       $ map (prettySymbol ga)
                       $ Set.toList hidSyms
                   _ -> []
      ++ case simplifyTh $ dgn_theory lbl of
        G_theory lid _ _ thsens _ -> let
                 (axs, thms) = OMap.partition isAxiom thsens
                 in subnodes "Axioms"
                    (map (mkAxDocNode ga . print_named lid) $ toNamedList axs)
                    ++ subnodes "Theorems"
                    (map (\ (s, t) -> mkThmNode ga
                            (print_named lid $ toNamed s t)
                            (isProvenSenStatus t)
                         ) $ OMap.toList thms)

mkThmNode :: GlobalAnnos -> Doc -> Bool -> Element
mkThmNode ga d a = add_attr
  (mkProvenAttr a) . unode "Theorem" . show $ useGlobalAnnos ga d

-- | a status may be open, proven or outdated
mkStatusAttr :: String -> Attr
mkStatusAttr = mkAttr "status"

mkProvenAttr :: Bool -> Attr
mkProvenAttr b = mkStatusAttr $ if b then "proven" else "open"

mkAxDocNode :: GlobalAnnos -> Doc -> Element
mkAxDocNode ga = unode "Axiom" . show . useGlobalAnnos ga

consStatus :: ConsStatus -> [Element]
consStatus cs = case getConsOfStatus cs of
  None -> []
  cStat -> [unode "ConsStatus" $ show cStat]

ledge :: GlobalAnnos -> DGraph -> LEdge DGLinkLab -> Element
ledge ga dg (f, t, lbl) = let
  typ = dgl_type lbl
  mor = gmorph ga $ dgl_morphism lbl
  mkMor n = add_attr (mkAttr "morphismsource" $ getNameOfNode n dg) mor
  lnkSt = case thmLinkStatus typ of
         Nothing -> []
         Just tls -> case tls of
            LeftOpen -> []
            Proven r ls -> dgrule r ++ map (\ e ->
                add_attr (mkAttr "linkref" $ showEdgeId e)
                $ unode "ProofBasis" ()) (Set.toList $ proofBasis ls)
  in add_attrs
  [ mkAttr "source" $ getNameOfNode f dg
  , mkAttr "target" $ getNameOfNode t dg
  , mkAttr "linkid" $ showEdgeId $ dgl_id lbl ]
  $ unode "DGLink"
    $ unode "Type" (getDGLinkType lbl) : lnkSt
    ++ consStatus (getLinkConsStatus typ)
    ++ [case typ of
         HidingFreeOrCofreeThm _ n _ _ -> mkMor n
         FreeOrCofreeDefLink _ (JustNode ns) -> mkMor $ getNode ns
         _ -> mor]

dgrule :: DGRule -> [Element]
dgrule r =
  unode "Rule" (dgRuleHeader r)
  : case r of
      DGRuleLocalInference m ->
        map (\ (s, t) -> add_attrs [mkNameAttr s, mkAttr "renamedTo" t]
             $ unode "MovedTheorems" ()) m
      Composition es -> map (\ e ->
        add_attr (mkAttr "linkref" $ showEdgeId e)
        $ unode "Composition" ()) es
      DGRuleWithEdge _ e ->
        [ add_attr (mkAttr "linkref" $ showEdgeId e)
        $ unode "RuleTarget" () ]
      _ -> []

showSymbols :: DGNodeLab -> String
showSymbols lbl = showSymbolsTh $ dgn_theory lbl 

showSymbolsTh :: G_theory -> String
showSymbolsTh th = case th of
  G_theory lid (ExtSign sig _) _ sens _ ->
     ppTopElement . add_attr (mkAttr "logic" $ language_name lid)
     $ unode "Ontology"
     [ unode "Symbols" . map (showSym lid)
           $ symlist_of lid sig
     , unode "Axioms" . map (\ ns ->
           add_attrs
             (mkNameAttr (senAttr ns) : mkAttr "text" (showDoc (sentence ns) "") :
             rangeAttrs (getRangeSpan $ sentence ns))
           . unode "Axiom" $ map (showSym lid)
            . symsOfSen lid $ sentence ns)
            $ toNamedList sens ]

showSym :: (Sentences lid sentence sign morphism symbol) =>
           lid -> symbol -> Element
showSym lid s = add_attrs
            [ mkNameAttr . show $ sym_name lid s
            , mkAttr "kind" $ symKind lid s]
            $ prettySymbol emptyGlobalAnnos s