{- |
Module      :  $Header$
Description :  pretty printing (parts of) a LibEnv
Copyright   :  (c) C. Maeder, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(DevGraph)

pretty printing (parts of) a LibEnv
-}

module Static.PrintDevGraph
    ( prettyLibEnv
    , printTh
    , prettyHistElem
    , prettyHistory
    , prettyGr
    , prettyLEdge
    , showLEdge
    , dgOriginHeader
    , dgOriginSpec
    , showXPath
    , dgLinkOriginHeader
    , dgLinkOriginSpec
    , dgRuleHeader
    , dgRuleEdges
    ) where

import Syntax.Print_AS_Structured ()
import Syntax.AS_Structured

import Static.GTheory
import Static.DevGraph
import Static.History

import Common.GlobalAnnotations
import Common.LibName
import Common.Id
import Common.Consistency
import Common.Doc as Doc
import Common.DocUtils
import Common.Result
import Common.Keywords
import Common.ConvertGlobalAnnos
import Common.AnalyseAnnos
import qualified Common.Lib.SizedList as SizedList
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.Graph as Tree

import Data.Graph.Inductive.Graph as Graph
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List
import Data.Char

printTh :: GlobalAnnos -> SIMPLE_ID -> G_theory -> Doc
printTh oga sn g =
    let ga = removeProblematicListAnnos oga in
    useGlobalAnnos ga $ pretty ga $+$ prettyGTheorySL g $+$
    sep [if null (tokStr sn) then Doc.empty else
             keyword specS <+> sidDoc sn <+> equals, prettyGTheory g]

removeProblematicListAnnos :: GlobalAnnos -> GlobalAnnos
removeProblematicListAnnos ga = let
    is = Map.keysSet $ Rel.toMap $ prec_annos ga
    la = literal_annos ga
    nla = la { list_lit = Map.filterWithKey ( \ li _ ->
        let (op, cl, cs) = getListBrackets li in
          Set.null $ Set.filter ( \ (Id ts ics _) ->
              cs == ics && isPrefixOf op ts && isSuffixOf cl ts) is)
        $ list_lit la }
    Result _ (Just lm) = store_literal_map Map.empty $ convertLiteralAnnos nla
    in ga { literal_annos = nla
          , literal_map = lm }

-- * pretty instances

showXPathComp :: XPathPart -> String
showXPathComp c = case c of
  ElemName s -> s
  ChildIndex i -> "Spec[" ++ show i ++ "]"

showXPath :: [XPathPart] -> String
showXPath l = case l of
  [] -> "/"
  _ -> concatMap (('/' :) . showXPathComp) l

showNodeId :: Node -> String
showNodeId i = "node " ++ show i

instance Pretty NodeSig where
  pretty (NodeSig n sig) = fsep [ text (showNodeId n) <> colon, pretty sig ]

dgOriginSpec :: DGOrigin -> Maybe SIMPLE_ID
dgOriginSpec o = case o of
    DGInst n -> Just n
    DGFitView n -> Just n
    _ -> Nothing

dgOriginHeader :: DGOrigin -> String
dgOriginHeader o = case o of
    DGEmpty -> "empty-spec"
    DGBasic -> "foreign-basic-spec"
    DGBasicSpec _ _ -> "basic-spec"
    DGExtension -> "extension"
    DGLogicCoercion -> "logic-translation"
    DGTranslation _ -> "translation"
    DGUnion -> "union"
    DGRestriction _ -> "restriction"
    DGRevealTranslation -> "translation part of a revealing"
    DGFreeOrCofree v -> map toLower (show v) ++ "-spec"
    DGLocal -> "local-spec"
    DGClosed -> "closed-spec"
    DGLogicQual -> "spec with logic qualifier"
    DGData -> "data-spec"
    DGFormalParams -> "formal parameters"
    DGImports -> "arch import"
    DGInst _ -> "instantiation"
    DGFitSpec -> "fitting-spec"
    DGFitView _ -> "fitting-view"
    DGProof -> "proof-construct"
    DGNormalForm n -> "normal-form(" ++ shows n ")"
    DGintegratedSCC -> "OWL spec with integrated strongly connected components"
    DGFlattening -> "flattening"

instance Pretty DGOrigin where
  pretty o = text (dgOriginHeader o) <+> pretty (dgOriginSpec o)
    $+$ case o of
          DGBasicSpec gbs syms -> specBraces (pretty gbs) $+$
              if Set.null syms then Doc.empty else
                  text "new symbols:" $+$ pretty syms
          DGTranslation (Renamed r) -> pretty r
          DGRestriction (Restricted r) -> pretty r
          _ -> Doc.empty

instance Pretty DGNodeInfo where
  pretty c = case c of
    DGNode {} -> pretty $ node_origin c
    DGRef {} ->
      pretty (getLibId $ ref_libname c) <+> text (showNodeId $ ref_node c)

prettyDGNodeLab :: DGNodeLab -> Doc
prettyDGNodeLab l = sep [ text $ getDGNodeName l, pretty $ nodeInfo l]

instance Pretty DGNodeLab where
  pretty l = vcat
    [ text $ "xpath: " ++ showXPath (reverse $ xpath $ dgn_name l)
    , pretty $ getNodeConsStatus l
    , if hasOpenGoals l then text "has open goals" else
      if hasSenKind (const True) l then Doc.empty else text "locally empty"
    , if labelHasHiding l then text "has ingoing hiding link" else Doc.empty
    , case dgn_nf l of
        Nothing -> Doc.empty
        Just n -> text "normal form:" <+> text (showNodeId n)
    , text "origin:" $+$ pretty (nodeInfo l)
    , case dgn_sigma l of
        Nothing -> Doc.empty
        Just gm -> text "normal form inclusion:" $+$ pretty gm
    , text "local theory:"
    , pretty $ dgn_theory l]

instance Pretty EdgeId where
   pretty (EdgeId i) = text $ show i

dgLinkOriginSpec :: DGLinkOrigin -> Maybe SIMPLE_ID
dgLinkOriginSpec o = case o of
    DGLinkMorph n -> Just n
    DGLinkInst n _ -> Just n
    DGLinkInstArg n -> Just n
    DGLinkView n _ -> Just n
    DGLinkFitView n -> Just n
    DGLinkFitViewImp n -> Just n
    _ -> Nothing

dgLinkMapping :: DGLinkOrigin -> [G_mapping]
dgLinkMapping o = case o of
    DGLinkInst _ (Fitted l) -> l
    DGLinkView _ (Fitted l) -> l
    _ -> []

dgLinkOriginHeader :: DGLinkOrigin -> String
dgLinkOriginHeader o = case o of
    SeeTarget -> "see target"
    SeeSource -> "see source"
    DGImpliesLink -> "reversed implies link of extension"
    DGLinkExtension -> "extension"
    DGLinkTranslation -> "OMDoc translation"
    DGLinkClosedLenv -> "closed spec and local environment"
    DGLinkImports -> "OWL import"
    DGLinkMorph _ -> "instantiation morphism of"
    DGLinkInst _ _ -> "instantiation of"
    DGLinkInstArg _ -> "actual parameter of"
    DGLinkView _ _ -> "view"
    DGLinkFitView _ -> "fit source of"
    DGLinkFitViewImp _ -> "add import to source of"
    DGLinkProof -> "proof-link"
    DGLinkFlatteningUnion -> "flattening non-disjoint union"
    DGLinkFlatteningRename -> "flattening renaming"

instance Pretty DGLinkOrigin where
  pretty o = text (dgLinkOriginHeader o) <+> pretty (dgLinkOriginSpec o)
    $+$ ppWithCommas (dgLinkMapping o)

-- | only shows the edge and node ids
showLEdge :: LEdge DGLinkLab -> String
showLEdge (s, t, l) = "edge " ++ showEdgeId (dgl_id l)
  ++ " (" ++ showNodeId s ++ " --> " ++ show t ++ ")"

-- | only print the origin and parts of the type
prettyDGLinkLab :: (DGLinkLab -> Doc) -> DGLinkLab -> Doc
prettyDGLinkLab f l = fsep
  [ case dgl_origin l of
      SeeTarget -> Doc.empty
      o -> pretty o
  , f l ]

-- | print short edge information
prettyLEdge :: LEdge DGLinkLab -> Doc
prettyLEdge e@(_, _, l) = fsep
  [ text $ showLEdge e
  , prettyDGLinkLab (text . getDGLinkType) l
  , prettyThmLinkStatus $ dgl_type l ]

dgRuleEdges :: DGRule -> [LEdge DGLinkLab]
dgRuleEdges r = case r of
    DGRuleWithEdge _ l -> [l]
    Composition ls -> ls
    _ -> []

dgRuleHeader :: DGRule -> String
dgRuleHeader r = case r of
    DGRule str -> str
    DGRuleWithEdge str _ -> str
    DGRuleLocalInference _ -> "local-inference"
    Composition _ -> "composition"
    BasicInference _ _ -> "basic-inference"
    BasicConsInference _ _ -> "basic-cons-inference"

instance Pretty DGRule where
  pretty r = let es = dgRuleEdges r in fsep
    [ text (dgRuleHeader r) <> if null es then Doc.empty else colon, case r of
    DGRuleLocalInference m ->
        braces $ sepByCommas $ map (\ (s, t) ->
          let d = text s in if s == t then d else pairElems d $ text t) m
    BasicInference c bp -> fsep
      [ text $ "using comorphism '" ++ show c ++ "' with proof tree:"
      , text $ show bp]
    BasicConsInference c bp -> fsep
      [ text $ "using comorphism '" ++ show c ++ "' with proof tree:"
      , text $ show bp]
    _ -> case es of
      [] -> Doc.empty
      [(_, _, l)] -> prettyDGLinkLab (const Doc.empty) l
      _ -> pretty $ Set.fromList $ map (\ (_, _, l) -> dgl_id l) es]

instance Pretty ThmLinkStatus where
  pretty tls = case tls of
        LeftOpen -> Doc.empty
        Proven r ls -> let s = proofBasis ls in
          fcat [parens (pretty r), if Set.null s then Doc.empty else pretty s]

prettyThmLinkStatus :: DGLinkType -> Doc
prettyThmLinkStatus = maybe Doc.empty pretty . thmLinkStatus

instance Pretty ConsStatus where
   pretty (ConsStatus cons pc thm) = case max cons pc of
     None -> Doc.empty
     c -> text (show c) <> pretty thm

instance Pretty DGLinkType where
    pretty t = (case t of
       FreeOrCofreeDefLink v _ -> text $ show v
       _ -> Doc.empty)
         <> text (getDGEdgeTypeModIncName $ getHomEdgeType False True t)
               <> prettyThmLinkStatus t
               $+$ pretty (getLinkConsStatus t)

instance Pretty DGLinkLab where
  pretty l = vcat
    [ text "Origin:" <+> pretty (dgl_origin l)
    , text "Type:" <+> pretty (dgl_type l)
    , text "Signature Morphism:"
    , if dglPending l then text "proof chain incomplete" else Doc.empty
    , pretty $ dgl_morphism l
    , case dgl_type l of
        HidingFreeOrCofreeThm k gm _ -> text ("with " ++ (case k of
          Nothing -> "hiding"
          Just v -> map toLower (show v))
          ++ " morphism:") $+$ pretty gm
        _ -> Doc.empty ]

-- | pretty print a labelled node
prettyGenLNode :: (a -> Doc) -> LNode a -> Doc
prettyGenLNode f (n, l) = fsep [text (showNodeId n) <> colon, f l]

prettyLNode :: LNode DGNodeLab -> Doc
prettyLNode = prettyGenLNode prettyDGNodeLab

dgChangeType :: DGChange -> String
dgChangeType c = case c of
    InsertNode _ -> "insert"
    DeleteNode _ -> "delete"
    InsertEdge _ -> "insert"
    DeleteEdge _ -> "delete"
    SetNodeLab _ _ -> "change"

instance Pretty DGChange where
  pretty c = text (dgChangeType c) <+> case c of
    InsertNode n -> prettyLNode n
    DeleteNode n -> prettyLNode n
    InsertEdge e -> prettyLEdge e
    DeleteEdge e -> prettyLEdge e
    SetNodeLab _ n -> prettyLNode n

prettyGr :: Tree.Gr DGNodeLab DGLinkLab -> Doc
prettyGr g = vcat (map prettyLNode $ labNodes g)
  $+$ vcat (map prettyLEdge $ labEdges g)

prettyImport :: MaybeNode -> Doc
prettyImport imp = case imp of
  EmptyNode _ -> Doc.empty
  JustNode n -> keyword givenS <+> pretty (getNode n)

prettyAllParams :: MaybeNode -> Doc
prettyAllParams ps = case ps of
  EmptyNode _ -> Doc.empty
  JustNode n -> pretty (getNode n)

instance Pretty ExtGenSig where
  pretty (ExtGenSig (GenSig imp params allParamSig) body) = fsep $
    pretty (getNode body) :
    (if null params then [] else
         [ pretty $ map getNode params
         , prettyAllParams allParamSig ]) ++
    [ prettyImport imp ]

instance Pretty ExtViewSig where
  pretty (ExtViewSig src gmor ptar) = fsep
    [ pretty (getNode src) <+> text toS
    , pretty ptar
    , pretty gmor ]

instance Pretty UnitSig where
  pretty (UnitSig params usig) =
    (if null params then Doc.empty else pretty $ map getNode params)
    <+> pretty (getNode usig)

instance Pretty ImpUnitSigOrSig where
  pretty iu = case iu of
    ImpUnitSig imp usig -> fsep
      [ pretty usig, prettyImport imp ]
    Sig n -> keyword specS <+> pretty (getNode n)

instance Pretty ArchSig where
  pretty (ArchSig m usig) = fsep
    [ printMap id vcat (\ k v -> fsep [keyword unitS <+> k <+> mapsto, v]) m
    , pretty usig ]

instance Pretty GlobalEntry where
  pretty ge = case ge of
    SpecEntry se -> topKey specS <+> pretty se
    ViewEntry ve -> topKey viewS <+> pretty ve
    UnitEntry ue -> topKey unitS <+> pretty ue
    ArchEntry ae -> topKey archS <+> pretty ae
    RefEntry -> keyword refinementS

instance Pretty DGraph where
  pretty dg = vcat
    [ prettyGr $ dgBody dg
    , text "global environment:"
    , printMap id vcat (\ k v -> fsep [k <+> mapsto, v]) $ globalEnv dg
    , text "history:"
    , prettyHistory $ reverseHistory $ proofHistory dg
    , text "redoable history:"
    , prettyHistory $ SizedList.reverse $ reverseHistory $ redoHistory dg
    , text "next edge:" <+> pretty (getNewEdgeId dg) ]

prettyHistElem :: HistElem -> Doc
prettyHistElem he = case he of
  HistElem c -> pretty c
  HistGroup r l -> text "rule:" <+> pretty r $+$ space <+> prettyHistory l

prettyHistory :: ProofHistory -> Doc
prettyHistory = vcat . map prettyHistElem . SizedList.toList

prettyLibEnv :: LibEnv -> Doc
prettyLibEnv = printMap id vsep ($+$)

