{- |
Module      :  ./Static/ToJson.hs
Description :  json output of Hets development graphs
Copyright   :  (c) Christian Maeder, DFKI GmbH 2014
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

Json of Hets DGs
-}

module Static.ToJson
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
import Common.Json

import Data.Graph.Inductive.Graph as Graph
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set (toList)

{- |
Export the development graph as json. If the flag full is True then
symbols for all nodes are shown as declarations, otherwise (the
default) only declaration for basic spec nodes are shown as is done
for the corresponding xml output. -}
dGraph :: HetcatsOpts -> LibEnv -> LibName -> DGraph -> Json
dGraph opts lenv ln dg =
  let body = dgBody dg
      ga = globalAnnos dg
      lnodes = labNodes body
      ledges = labEdges body
  in tagJson "DGraph" $ mkJObj
         [ mkJPair "filename" $ getFilePath ln
         , mkJPair "mime-type" . fromMaybe "unknown" $ mimeType ln
         , mkJPair "libname" . show $ setAngles False $ getLibId ln
         , ("dgnodes", mkJNum $ length lnodes)
         , ("dgedges", mkJNum $ length ledges)
         , ("nextlinkid", mkJNum . getEdgeNum $ getNewEdgeId dg)
         , ("Global", mkJArr . map (anToJson ga) . convertGlobalAnnos
                            $ removeDOLprefixes ga)
         , ("DGNode", mkJArr $ map (lnode opts ga lenv) lnodes)
         , ("DGLink", mkJArr $ map (ledge opts ga dg) ledges) ]

gmorph :: HetcatsOpts -> GlobalAnnos -> GMorphism -> Json
gmorph opts ga gm@(GMorphism cid (ExtSign ssig _) _ tmor _) =
  case map_sign cid ssig of
    Result _ mr -> case mr of
      Nothing -> error $ "Static.ToXml.gmorph: " ++ showGlobalDoc ga gm ""
      Just (tsig, tsens) -> let
        tid = targetLogic cid
        sl = Map.toList . Map.filterWithKey (/=) $ symmap_of tid tmor
        in mkJObj
        $ mkNameJPair (language_name cid)
        : [("ComorphismAxioms", mkJArr
            $ map (showSen opts (targetLogic cid) ga Nothing tsig) tsens)
          | not (fullTheories opts) && not (null tsens) ]
        ++ [("Map", mkJArr $
             map (\ (s, t) -> mkJObj
             [("map", showSym tid s), ("to", showSym tid t)]) sl)
           | not $ null sl]

prettySymbol :: (GetRange a, Pretty a) => GlobalAnnos -> a -> [JPair]
prettySymbol = rangedToJson "Symbol"

lnode :: HetcatsOpts -> GlobalAnnos -> LibEnv -> LNode DGNodeLab -> Json
lnode opts ga lenv (_, lbl) =
  let nm = dgn_name lbl
      (spn, xp) = case reverse $ xpath nm of
          ElemName s : t -> (s, showXPath t)
          l -> ("?", showXPath l)
  in mkJObj
  $ mkNameJPair (showName nm)
    : rangeToJPair (srcRange nm)
    ++ [("reference", mkJBool $ isDGRef lbl)]
    ++ case signOf $ dgn_theory lbl of
        G_sign slid _ _ -> mkJPair "logic" (show slid)
          : if not (isDGRef lbl) && dgn_origin lbl < DGProof then
             [mkJPair "refname" spn, mkJPair "relxpath" xp ]
            else []
    ++ case nodeInfo lbl of
          DGRef li rf ->
            [ ("Reference", mkJObj
              [ mkJPair "library" $ show $ setAngles False $ getLibId li
              , mkJPair "location" $ getFilePath li
              , mkJPair "node" $ getNameOfNode rf $ lookupDGraph li lenv ])]
          DGNode orig cs -> consStatus cs ++ case orig of
                   DGBasicSpec _ (G_sign lid (ExtSign dsig _) _) _ ->
                     let syms = mostSymsOf lid dsig in
                     [ ("Declarations", mkJArr
                       $ map (showSym lid) syms) | not $ null syms ]
                   DGRestriction _ hidSyms ->
                     [ ("Hidden", mkJArr
                       . map (mkJObj . prettySymbol ga)
                       $ Set.toList hidSyms) ]
                   _ -> []
      ++ case dgn_theory lbl of
        G_theory lid _ (ExtSign sig _) _ thsens _ -> let
          (axs, thms) = OMap.partition isAxiom thsens
          nAxs = toNamedList axs
          nThms = OMap.toList thms
          in
          [("Symbols", mkJArr . map (showSym lid) $ symlist_of lid sig)
          | fullSign opts ]
          ++ [("Axioms", mkJArr
             $ map (showSen opts lid ga Nothing sig) nAxs) | not $ null nAxs ]
          ++ [("Theorems", mkJArr
             $ map (\ (s, t) -> showSen opts lid ga
                         (Just $ isProvenSenStatus t) sig $ toNamed s t)
                         nThms) | not $ null nThms]
          ++ if fullTheories opts then case globalTheory lbl of
               Just (G_theory glid _ _ _ allSens _) -> case
                   coerceThSens glid lid "xml-lnode" allSens of
                 Just gsens -> let
                   nSens = toNamedList
                     $ OMap.filter ((`notElem` map sentence
                                    (OMap.elems thsens)) . sentence) gsens
                     in [("ImpAxioms", mkJArr
                          $ map (showSen opts lid ga Nothing sig) nSens)
                        | not $ null nSens ]
                 _ -> []
               _ -> []
             else []

-- | a status may be open, proven or outdated
mkStatusJPair :: String -> JPair
mkStatusJPair = mkJPair "status"

mkProvenJPair :: Bool -> JPair
mkProvenJPair b = mkStatusJPair $ if b then "proven" else "open"

consStatus :: ConsStatus -> [JPair]
consStatus cs = case getConsOfStatus cs of
  None -> []
  cStat -> [("ConsStatus", mkJStr $ show cStat)]

ledge :: HetcatsOpts -> GlobalAnnos -> DGraph -> LEdge DGLinkLab -> Json
ledge opts ga dg (f, t, lbl) = let
  typ = dgl_type lbl
  mor = gmorph opts ga $ dgl_morphism lbl
  mkMor n = [mkJPair "morphismsource" $ getNameOfNode n dg]
  lnkSt = case thmLinkStatus typ of
         Nothing -> []
         Just tls -> case tls of
            LeftOpen -> []
            Proven r ls -> dgrule r
              ++ let bs = Set.toList $ proofBasis ls in
                 [("ProofBasis", mkJArr
                   $ map (mkJNum . getEdgeNum) bs) | not $ null bs]
  in mkJObj
  $ [ mkJPair "source" $ getNameOfNode f dg
  , mkJPair "target" $ getNameOfNode t dg
  , ("linkid", mkJNum . getEdgeNum $ dgl_id lbl) ]
  ++ case dgl_origin lbl of
         DGLinkView i _ ->
           [mkNameJPair . iriToStringShortUnsecure $ setAngles False i]
         _ -> []
  ++ mkJPair "Type" (getDGLinkType lbl) : lnkSt
    ++ consStatus (getLinkConsStatus typ)
    ++ case typ of
         HidingFreeOrCofreeThm _ n _ _ -> mkMor n
         FreeOrCofreeDefLink _ (JustNode ns) -> mkMor $ getNode ns
         _ -> []
    ++ [("GMorphism", mor)]

dgrule :: DGRule -> [JPair]
dgrule r =
  mkJPair "Rule" (dgRuleHeader r)
  : case r of
      DGRuleLocalInference m -> [("MovedTheorems", mkJArr
        $ map (\ (s, t) -> mkJObj [mkNameJPair s, mkJPair "renamedTo" t]) m)]
      Composition es ->
        [("Composition", mkJArr $ map (mkJNum . getEdgeNum) es)]
      DGRuleWithEdge _ e -> [("RuleTarget", mkJNum $ getEdgeNum e)]
      _ -> []

-- | collects all symbols from dg and displays them as json
dgSymbols :: HetcatsOpts -> DGraph -> Json
dgSymbols opts dg = let ga = globalAnnos dg in tagJson "Ontologies"
  $ mkJArr $ map (\ (i, lbl) -> let ins = getImportNames dg i in
    showSymbols opts ins ga lbl) $ labNodesDG dg

showSymbols :: HetcatsOpts -> [String] -> GlobalAnnos -> DGNodeLab -> Json
showSymbols opts ins ga lbl = showSymbolsTh opts ins (getDGNodeName lbl) ga
  $ dgn_theory lbl

showSymbolsTh :: HetcatsOpts -> [String] -> String -> GlobalAnnos -> G_theory -> Json
showSymbolsTh opts ins name ga th = case th of
  G_theory lid _ (ExtSign sig _) _ sens _ -> mkJObj
     [ mkJPair "logic" $ language_name lid
     , mkNameJPair name
     , ("Ontology", mkJObj
       [ ("Symbols", mkJArr . map (showSym lid) $ symlist_of lid sig)
       , ("Axioms", mkJArr . map (showSen opts lid ga Nothing sig)
         $ toNamedList sens)
       , ("Import", mkJArr $ map mkJStr ins) ])]

showSen :: ( GetRange sentence, Pretty sentence
           , Sentences lid sentence sign morphism symbol) =>
   HetcatsOpts -> lid -> GlobalAnnos -> Maybe Bool -> sign -> Named sentence -> Json
showSen opts lid ga mt sig ns = let s = sentence ns in mkJObj
    $ case mt of
       Nothing -> []
       Just b -> [mkProvenJPair b]
     ++ mkNameJPair (senAttr ns) : rangeToJPair (getRangeSpan s)
     ++ case priority ns of
          Just p -> [mkPriorityJPair p]
          _ -> []
     ++ mkJPair (if isJust mt then "Theorem" else "Axiom")
          (show . useGlobalAnnos ga . print_named lid
                            . makeNamed "" $ simplify_sen lid sig s)
          : (let syms = symsOfSen lid sig s in
              [("SenSymbols", mkJArr $ map (showSym lid) syms)
               | not $ null syms])
          ++ case senMark ns of
               "" -> []
               m -> [mkJPair "ComorphismOrigin" m]
          ++ if printAST opts
             then [("AST", asJson s)]
             else []

showSym :: Sentences lid sentence sign morphism symbol => lid -> symbol -> Json
showSym lid s = mkJObj
  $ [ mkJPair "kind" $ symKind lid s
    , mkNameJPair . show $ sym_name lid s
    , mkJPair "iri" $ fullSymName lid s ]
    ++ prettySymbol emptyGlobalAnnos s
