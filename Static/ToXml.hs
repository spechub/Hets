{- |
Module      :  ./Static/ToXml.hs
Description :  xml output of Hets development graphs
Copyright   :  (c) Ewaryst Schulz, Uni Bremen 2009
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

Xml of Hets DGs
-}

module Static.ToXml
  ( dGraph
  , lnode
  , dgSymbols
  , showSymbols
  , showSymbolsTh
  ) where

import Driver.Options

import Static.DgUtils
import Static.DevGraph
import Static.GTheory
import Static.ComputeTheory (getImportNames)
import Static.PrintDevGraph

import Logic.Prover
import Logic.Logic
import Logic.Comorphism
import Logic.Grothendieck

import Common.AS_Annotation
import Common.ConvertGlobalAnnos
import Common.Consistency
import Common.DocUtils
import Common.ExtSign
import Common.GlobalAnnotations
import Common.Id
import Common.IRI
import Common.LibName
import qualified Common.OrderedMap as OMap
import Common.Result
import Common.ToXml

import Text.XML.Light

import Data.Graph.Inductive.Graph as Graph
import Data.Maybe
import qualified Data.HashMap.Strict as Map
import qualified Data.HashSet as Set (toList)
import Data.Char (toLower)

{- |
Export the development graph as xml. If the flag full is True then
symbols for all nodes are shown as declarations, otherwise (the
default) only declaration for basic spec nodes are shown that are
sufficient to reconstruct the development from the xml output. -}
dGraph :: HetcatsOpts -> LibEnv -> LibName -> DGraph -> Element
dGraph opts lenv ln dg =
  let body = dgBody dg
      ga = globalAnnos dg
      lnodes = labNodes body
      ledges = labEdges body
  in add_attrs [ mkAttr "filename" $ getFilePath ln
               , mkAttr "mime-type" . fromMaybe "unknown" $ mimeType ln
               , mkAttr "libname" . show $ setAngles False $ getLibId ln
               , mkAttr "dgnodes" . show $ length lnodes
               , mkAttr "dgedges" . show $ length ledges
               , mkAttr "nextlinkid" . showEdgeId $ getNewEdgeId dg ]
     . unode "DGraph" $
         subnodes "Global" (annotations ga . convertGlobalAnnos
                            $ removeDOLprefixes ga)
         ++ map (lnode opts ga lenv) lnodes
         ++ map (ledge opts ga dg) ledges

gmorph :: HetcatsOpts -> GlobalAnnos -> GMorphism -> Element
gmorph opts ga gm@(GMorphism cid (ExtSign ssig _) _ tmor _) =
  case map_sign cid ssig of
    Result _ mr -> case mr of
      Nothing -> error $ "Static.ToXml.gmorph: " ++ showGlobalDoc ga gm ""
      Just (tsig, tsens) -> let
        tid = targetLogic cid
        sl = Map.toList . Map.filterWithKey (/=) $ symmap_of tid tmor
        in add_attr (mkNameAttr $ language_name cid)
           $ unode "GMorphism" $
             (if fullTheories opts then [] else subnodes "ComorphismAxioms"
             $ map (showSen opts (targetLogic cid) ga Nothing tsig) tsens)
             ++ map (\ (s, t) -> unode "map" [showSym tid s, showSym tid t]) sl

prettyRangeElem :: (GetRange a, Pretty a) => String -> GlobalAnnos -> a
                -> Element
prettyRangeElem s ga a =
  add_attrs (rangeAttrs $ getRangeSpan a) $ prettyElem s ga a

prettySymbol :: (GetRange a, Pretty a) => GlobalAnnos -> a -> Element
prettySymbol = prettyRangeElem "Symbol"

lnode :: HetcatsOpts -> GlobalAnnos -> LibEnv -> LNode DGNodeLab -> Element
lnode opts ga lenv (nodeId, lbl) =
  let nm = dgn_name lbl
      (spn, xp) = case reverse $ xpath nm of
          ElemName s : t -> (s, showXPath t)
          l -> ("?", showXPath l)
  in add_attrs (mkNameAttr (showName nm)
    : rangeAttrs (srcRange nm)
    ++ [mkAttr "id" $ show nodeId]
    ++ [mkAttr "internal" (map toLower $ show $ isInternal nm)]
    ++ mkAttr "reference" (map toLower $ show $ isDGRef lbl)
    : case signOf $ dgn_theory lbl of
        G_sign slid _ _ -> mkAttr "logic" (show slid)
          : if not (isDGRef lbl) && dgn_origin lbl < DGProof then
             [mkAttr "refname" spn, mkAttr "relxpath" xp ]
            else [])
  $ unode "DGNode"
    $ case nodeInfo lbl of
          DGRef li rf ->
            [ add_attrs
              [ mkAttr "library" $ show $ setAngles False $ getLibId li
              , mkAttr "location" $ getFilePath li
              , mkAttr "node" $ getNameOfNode rf $ lookupDGraph li lenv ]
            $ unode "Reference" () ]
          DGNode orig cs -> consStatus cs ++ case orig of
                   DGBasicSpec _ (G_sign lid (ExtSign dsig _) _) _ ->
                     subnodes "Declarations"
                       $ map (showSym lid)
                       $ mostSymsOf lid dsig
                   DGRestriction _ hidSyms -> subnodes "Hidden"
                       $ map (prettySymbol ga)
                       $ Set.toList hidSyms
                   _ -> []
      ++ case dgn_theory lbl of
        G_theory lid _ (ExtSign sig _) _ thsens _ -> let
          (axs, thms) = OMap.partition isAxiom thsens in
          (if fullSign opts
           then subnodes "Symbols" (map (showSym lid) $ symlist_of lid sig)
           else [])
          ++ subnodes "Axioms"
                    (map (showSen opts lid ga Nothing sig) $ toNamedList axs)
          ++ subnodes "Theorems"
                    (map (\ (s, t) -> showSen opts lid ga
                         (Just $ isProvenSenStatus t) sig $ toNamed s t)
                         $ OMap.toList thms)
          ++ if fullTheories opts then case globalTheory lbl of
               Just (G_theory glid _ _ _ allSens _) -> case
                   coerceThSens glid lid "xml-lnode" allSens of
                 Just gsens -> subnodes "ImpAxioms"
                    $ map (showSen opts lid ga Nothing sig) $ toNamedList
                     $ OMap.filter ((`notElem` map sentence
                                    (OMap.elems thsens)) . sentence) gsens
                 _ -> []
               _ -> []
             else []

-- | a status may be open, proven or outdated
mkStatusAttr :: String -> Attr
mkStatusAttr = mkAttr "status"

mkProvenAttr :: Bool -> Attr
mkProvenAttr b = mkStatusAttr $ if b then "proven" else "open"

consStatus :: ConsStatus -> [Element]
consStatus cs = case getConsOfStatus cs of
  None -> []
  cStat -> [unode "ConsStatus" $ show cStat]

ledge :: HetcatsOpts -> GlobalAnnos -> DGraph -> LEdge DGLinkLab -> Element
ledge opts ga dg (f, t, lbl) = let
  typ = dgl_type lbl
  mor = gmorph opts ga $ dgl_morphism lbl
  mkMor n = add_attr (mkAttr "morphismsource" $ getNameOfNode n dg) mor
  lnkSt = case thmLinkStatus typ of
         Nothing -> []
         Just tls -> case tls of
            LeftOpen -> []
            Proven r ls -> dgrule r ++ map (\ e ->
                add_attr (mkAttr "linkref" $ showEdgeId e)
                $ unode "ProofBasis" ()) (Set.toList $ proofBasis ls)
  in add_attrs
  ([ mkAttr "source" $ getNameOfNode f dg
  , mkAttr "target" $ getNameOfNode t dg
  , mkAttr "linkid" $ showEdgeId $ dgl_id lbl
  , mkAttr "id_source" $ show f
  , mkAttr "id_target" $ show t
  ] ++ case dgl_origin lbl of
         DGLinkView i _ ->
           [mkNameAttr . iriToStringShortUnsecure $ setAngles False i]
         _ -> [])
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

-- | collects all symbols from dg and displays them as xml
dgSymbols :: HetcatsOpts -> DGraph -> Element
dgSymbols opts dg = let ga = globalAnnos dg in unode "Ontologies"
  $ map (\ (i, lbl) -> let ins = getImportNames dg i in
    showSymbols opts ins ga lbl) $ labNodesDG dg

showSymbols :: HetcatsOpts -> [String] -> GlobalAnnos -> DGNodeLab -> Element
showSymbols opts ins ga lbl = showSymbolsTh opts ins (getDGNodeName lbl) ga
  $ dgn_theory lbl

showSymbolsTh :: HetcatsOpts -> [String] -> String -> GlobalAnnos -> G_theory -> Element
showSymbolsTh opts ins name ga th = case th of
  G_theory lid _ (ExtSign sig _) _ sens _ -> add_attrs
     [ mkAttr "logic" $ language_name lid
     , mkNameAttr name ]
     . unode "Ontology"
     $ [ unode "Symbols" . map (showSym lid) $ symlist_of lid sig
       , unode "Axioms" . map (showSen opts lid ga Nothing sig) $ toNamedList sens ]
     ++ map (unode "Import") ins

showSen :: ( GetRange sentence, Pretty sentence
           , Sentences lid sentence sign morphism symbol) =>
   HetcatsOpts -> lid -> GlobalAnnos -> Maybe Bool -> sign -> Named sentence -> Element
showSen opts lid ga mt sig ns =
 let s = sentence ns in add_attrs
    (case mt of
       Nothing -> []
       Just b -> [mkProvenAttr b]
     ++ mkNameAttr (senAttr ns) : rangeAttrs (getRangeSpan s)
     ++ case priority ns of
         Just impo -> [mkPriorityAttr impo]
         _ -> [])
    . unode (if isJust mt then "Theorem" else "Axiom") $ unode "Text"
          (show . useGlobalAnnos ga . print_named lid
                            . makeNamed "" $ simplify_sen lid sig s)
          : map (showSym lid) (symsOfSen lid sig s)
          ++ case senMark ns of
               "" -> []
               m -> [unode "ComorphismOrigin" m]
          ++ if printAST opts
             then [unode "AST" $ asXml s]
             else []

showSym :: (Sentences lid sentence sign morphism symbol) =>
           lid -> symbol -> Element
showSym lid s = add_attrs ((reverse
            . maybe id ((:) . mkAttr "label") (sym_label lid s))
            [ mkAttr "iri" $ fullSymName lid s
            , mkNameAttr . show $ sym_name lid s
            , mkAttr "kind" $ symKind lid s
            ]) $ prettySymbol emptyGlobalAnnos s
