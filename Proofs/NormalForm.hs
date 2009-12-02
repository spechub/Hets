{- |
Module      :  $Header$
Description :  compute the normal forms of all nodes in development graphs
Copyright   :  (c) Christian Maeder, DFKI GmbH 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

compute normal forms
-}

module Proofs.NormalForm
    ( normalFormLibEnv
    , normalForm
    , freeness
    , theoremFreeShift
    , theoremFreeShiftFromList
    ) where

import Logic.Logic
import Logic.Grothendieck
import Logic.Coerce
import Logic.Comorphism
import Logic.Prover(toNamedList, toThSens)
import Logic.ExtSign

import Static.ComputeTheory
import Static.GTheory
import Static.DevGraph
import Static.WACocone

import Proofs.EdgeUtils
import Proofs.ComputeColimit

import Common.Consistency
import Common.ExtSign
import Common.Id
import Common.LibName
import Common.Result
import Common.Lib.Graph

import Data.Graph.Inductive.Graph as Graph
import qualified Data.Map as Map
import Data.List (nub)
import Control.Monad
import Comorphisms.LogicGraph

import Data.Maybe
import Proofs.SimpleTheoremHideShift(getInComingGlobalUnprovenEdges)
import Debug.Trace

normalFormRule :: DGRule
normalFormRule = DGRule "NormalForm"

-- | compute normal form for a library and imported libs
normalForm :: LibName -> LibEnv -> Result LibEnv
normalForm ln le = normalFormLNS (dependentLibs ln le) le

-- | compute norm form for all libraries
normalFormLibEnv :: LibEnv -> Result LibEnv
normalFormLibEnv le = normalFormLNS (getTopsortedLibs le) le

normalFormLNS :: [LibName] -> LibEnv -> Result LibEnv
normalFormLNS lns libEnv = foldM (\ le ln -> do
  let dg = lookupDGraph ln le
  newDg <- normalFormDG le dg
  return $ Map.insert ln
    (groupHistory dg normalFormRule newDg) le)
  libEnv lns

normalFormDG :: LibEnv -> DGraph -> Result DGraph
normalFormDG libEnv dgraph = foldM (\ dg (node, nodelab) ->
  if labelHasHiding nodelab then case dgn_nf nodelab of
    Just _ -> return dg -- already computed
    Nothing -> if isDGRef nodelab then do
        -- the normal form of the node
        -- is a reference to the normal form of the node it references
        -- careful: here not refNf, but a new Node which references refN
       let refLib = dgn_libname nodelab
           refNode = dgn_node nodelab
           refGraph' = lookupDGraph refLib libEnv
           refLabel = labDG refGraph' refNode
       case dgn_nf refLabel of
         Nothing -> warning dg
           (getDGNodeName refLabel ++ " (node " ++ show refNode
            ++ ") from '" ++ show (getLibId refLib)
            ++ "' without normal form") nullRange
         Just refNf -> do
           let refNodelab = labDG refGraph' refNf
               -- the label of the normal form ^
               nfNode = getNewNodeDG dg
               -- the new reference node in the old graph ^
               refLab = refNodelab
                 { dgn_name = extName "NormalForm" $ dgn_name nodelab
                 , dgn_nf = Just nfNode
                 , dgn_sigma = Just $ ide $ dgn_sign refNodelab
                 , nodeInfo = newRefInfo refLib refNf
                 , dgn_lock = Nothing }
               newLab = nodelab
                 { dgn_nf = Just nfNode,
                   dgn_sigma = dgn_sigma refLabel }
               chLab = SetNodeLab nodelab (node, newLab)
               changes = [InsertNode (nfNode, refLab), chLab]
               newGraph = changesDGH dgraph changes
           return newGraph
      else do
        let gd = insNode (node, dgn_theory nodelab) empty
            g0 = Map.fromList [(node, node)]
            (diagram, g) = computeDiagram dg [node] (gd, g0)
            fsub = finalSubcateg diagram
            Result ds res = gWeaklyAmalgamableCocone fsub
            es = map (\ d -> if isErrorDiag d then d { diagKind = Warning }
                             else d) ds
        appendDiags es
        case res of
          Nothing -> warning dg
                ("cocone failure for " ++ getDGNodeName nodelab
                 ++ " (node " ++ shows node ")") nullRange
          Just (sign, mmap) -> do
            -- we don't know that node is in fsub
            -- if it's not, we have to find a tip accessible from node
            -- and dgn_sigma = edgeLabel(node, tip); mmap (g Map.! tip)
            morNode <- if node `elem` nodes fsub then let
                        gn = Map.findWithDefault (error "gn") node g
                        phi = Map.findWithDefault (error "mor") gn mmap
                       in return phi else let
                          leaves = filter (\x -> outdeg fsub x == 0) $
                                     nodes fsub
                          paths =  map (\(x, Result _ (Just f)) -> (x,f)) $
                                      map (\x ->
                                              (x, dijkstra diagram node x)) $
                                      filter (\x -> node `elem` subgraph
                                                      diagram x) leaves
                                          in
                            case paths of
                             [] -> fail "node should reach a tip"
                             (xn, xf) : _ -> comp xf $ mmap Map.! xn
            let nfNode = getNewNodeDG dg -- new node for normal form
                info = nodeInfo nodelab
                ConsStatus c cp pr = node_cons_status info
                nfLabel = newInfoNodeLab
                  (extName "NormalForm" $ dgn_name nodelab)
                  info
                  { node_origin = DGNormalForm node
                  , node_cons_status = mkConsStatus c }
                  sign
                newLab = nodelab -- the new label for node
                     { dgn_nf = Just nfNode
                     , dgn_sigma = Just morNode
                     , nodeInfo = info
                         { node_cons_status = ConsStatus None cp pr }
                     }
            -- add the nf to the label of node
                chLab = SetNodeLab nodelab (node, newLab)
            -- insert the new node and add edges from the predecessors
                insNNF = InsertNode (nfNode, nfLabel)
                makeEdge src tgt m = (src, tgt, globDefLink m DGLinkProof)
                insStrMor = map (\ (x, f) -> InsertEdge $ makeEdge x nfNode f)
                  $ nub $ map (\ (x, y) -> (g Map.! x, y))
                  $ (node, morNode) : Map.toList mmap
                allChanges = insNNF : chLab : insStrMor
                newDG = changesDGH dg allChanges
            return $ changeDGH newDG $ SetNodeLab nfLabel (nfNode, nfLabel
              { globalTheory = computeLabelTheory libEnv newDG
                (nfNode, nfLabel) })
  else return dg) dgraph $ topsortedNodes dgraph -- only change relevant nodes

{- | computes the diagram associated to a node N in a development graph,
   adding common origins for multiple occurences of nodes, whenever
   needed
-}
computeDiagram :: DGraph -> [Node] -> (GDiagram, Map.Map Node Node)
               -> (GDiagram, Map.Map Node Node)
  -- as described in the paper for now
computeDiagram dgraph nodeList (gd, g) =
 case nodeList of
  [] -> (gd, g)
  _ ->
   let -- defInEdges is list of pairs (n, edges of target g(n))
       defInEdges = map (\n -> (n,filter (\e@(s,t,_) -> s /= t &&
                         liftE (liftOr isGlobalDef isHidingDef) e) $
                        innDG dgraph $ g Map.! n))  nodeList
       -- TO DO: no local links, and why edges with s=t are removed
       --        add normal form nodes
       -- sources of each edge must be added as new nodes
       nodeIds = zip (newNodes (length $ concatMap snd defInEdges) gd)
                     $ concatMap (\(n,l) -> map (\x -> (n,x)) l ) defInEdges
       newLNodes = zip (map fst nodeIds) $
                   map (\ (s,_,_) -> dgn_theory $ labDG dgraph s) $
                   concatMap snd defInEdges
       g0 = Map.fromList $
                     map (\ (newS, (_newT, (s,_t, _))) -> (newS,s)) nodeIds
       morphEdge (n1,(n2, (_, _, el))) =
         if isHidingDef $ dgl_type el
            then (n2, n1, (x, dgl_morphism el))
            else (n1, n2, (x, dgl_morphism el))
         where EdgeId x = dgl_id el
       newLEdges = map morphEdge nodeIds
       gd' = insEdges newLEdges $ insNodes newLNodes gd
       g' = Map.union g g0
   in computeDiagram dgraph (map fst nodeIds) (gd', g')

finalSubcateg :: GDiagram -> GDiagram
finalSubcateg graph = let
    leaves = filter (\(n,_) -> outdeg graph n == 0)$ labNodes graph
 in buildGraph graph (map fst leaves) leaves [] $ nodes graph

subgraph :: Gr a b -> Node -> [Node]
subgraph graph node = let
   descs nList descList =
    case nList of
      [] -> descList
      _ -> let
             newDescs = concatMap (\x -> pre graph x) nList
             nList' = filter (\x -> not $ x `elem` nList) newDescs
             descList' = nub $ descList ++ newDescs
           in descs nList' descList'
 in descs [node] []

buildGraph :: GDiagram -> [Node]
           -> [LNode G_theory]
           -> [LEdge (Int, GMorphism)]
           -> [Node]
           -> GDiagram
buildGraph oGraph leaves nList eList nodeList =
 case nodeList of
  [] -> mkGraph nList eList
  n:nodeList' ->
     case outdeg oGraph n of
      1 -> buildGraph oGraph leaves nList eList nodeList'
       -- the node is simply removed
      0 -> buildGraph oGraph leaves nList eList nodeList'
       -- the leaves have already been added to nList
      _ -> let
            Just l = lab oGraph n
            nList' = (n, l):nList
            accesLeaves = filter (\x -> n `elem` subgraph oGraph x) leaves
            eList' = map ( \(x, Result _ (Just y)) -> (n,x,(1::Int,y))) $
                     map (\x -> (x, dijkstra oGraph n x)) accesLeaves
           in buildGraph oGraph leaves nList' (eList ++ eList') nodeList'
       -- branch, must add n to the nList and edges in eList

-- ********************************************************************
-- normalization of freeness
-- to be moved in a separate file, together with TheoremFreeShift
-- *********************************************************************
freeness :: LibName -> LibEnv -> Result LibEnv
freeness ln le = do
  let dg = lookupDGraph ln le
  newDg <- freenessDG le dg
  return $ Map.insert ln
    (groupHistory dg normalFormRule newDg) le

freenessDG :: LibEnv -> DGraph -> Result DGraph
freenessDG le dgraph = do
 foldM (handleEdge le) dgraph $ labEdgesDG dgraph

handleEdge :: LibEnv -> DGraph ->  LEdge DGLinkLab -> Result DGraph
handleEdge libEnv dg edge@(m,n,x) = do
    case dgl_type x of
     FreeOrCofreeDefLink _ _ -> do
      let phi = dgl_morphism x
          gth= dgn_theory $ labDG dg m
      case gth of
       G_theory lid sig _ sen _ -> do
        case phi of
         GMorphism cid _ _ mor1 _ -> do
          mor <- coerceMorphism (targetLogic cid) lid "free" mor1
          let res = quotient_term_algebra lid mor $ toNamedList sen
          case maybeResult res of
           Just (sigK, axK) -> do
               -- success in logic lid
            let thK = G_theory lid (makeExtSign lid sigK)
                             startSigId (toThSens axK) startThId
            incl <- subsig_inclusion lid (plainSign sig) sigK
            let inclM = gEmbed $ mkG_morphism lid incl
      -- remove x
      -- add nodes
      -- k  with signature = sigK, sentences axK
      -- global def link from m to k, labeled with inclusion
      -- hiding def link from k to n, labeled with inclusion
              --   m' = getNewNodeDG dg -- new node
                nodelab = labDG dg m
                info = nodeInfo nodelab
                ConsStatus c _ _ = node_cons_status info
                k = (getNewNodeDG dg)
                labelK = newInfoNodeLab
                   (extName "NormalForm" $ dgn_name nodelab)
                   info
                   { node_origin = DGNormalForm m
                  , node_cons_status = mkConsStatus c }
                  thK
                insK = InsertNode (k, labelK)
                insE = [ InsertEdge (m,k, globDefLink inclM DGLinkProof)
                       , InsertEdge (k, n, defDGLink inclM HidingDefLink
                                      DGLinkProof)]
                del = DeleteEdge edge
                allChanges = del: insK : insE
                newDG = changesDGH dg allChanges
                labelN = labDG dg n
            return $ changesDGH newDG $ [SetNodeLab labelK (k, labelK
              { globalTheory = computeLabelTheory libEnv newDG
                               (k, labelK) }),
              SetNodeLab labelN (n, labelN
              { globalTheory = computeLabelTheory libEnv newDG
                               (n, labelN)
                , labelHasHiding = True })
              ]
           _ -> do
               -- failed in logic lid, look for comorphism and translate
               -- then recursive call
              let look = lookupQTA_in_LG $ language_name lid
              case maybeResult look of
               Nothing -> return dg
                  -- can't translate to a logic where qta is implemented
               Just com -> do
                (m', dgM) <- translateFree libEnv dg edge com
                foldM (handleEdge libEnv) dgM $ out (dgBody dgM) m'
     _ -> return dg

translateFree :: LibEnv -> DGraph -> LEdge DGLinkLab -> AnyComorphism ->
                 Result (Node, DGraph)
translateFree le dg edge@(m,n,x) com = do
 (m', dg') <- translateNode le dg m (dgn_theory $ labDG dg m) com
 (n', dg'') <- translateNode le dg' n (dgn_theory $ labDG dg n) com
 dg''' <- translateEdge dg'' edge (dgl_morphism x) com m' n'
 return (m', dg''')

translateEdge :: DGraph -> LEdge DGLinkLab -> GMorphism -> AnyComorphism ->
              Node -> Node -> Result DGraph
translateEdge dg edge (GMorphism cid _sig _i1 mor1 _i2)
              (Comorphism cid') m n = do
 let
  lidS = sourceLogic cid'
  lidT = targetLogic cid'
 mor2 <- coerceMorphism (targetLogic cid) lidS "" mor1
 mor3 <- map_morphism cid' mor2
 let
   gm = gEmbed $ mkG_morphism lidT mor3
   del = DeleteEdge edge
   edge' = defDGLink gm
             (FreeOrCofreeDefLink Free $ EmptyNode $ Logic lidT)  DGLinkProof
   ins = InsertEdge (m, n, edge')
 return $ changesDGH dg [del, ins]

translateNode :: LibEnv -> DGraph -> Node -> G_theory -> AnyComorphism ->
                 Result (Node, DGraph)
translateNode libEnv dg n s@(G_theory lid sig _ _ _) com@(Comorphism cid) = do
 let
   m' = getNewNodeDG dg -- new node
   nodelab = labDG dg n
   info = nodeInfo nodelab
   ConsStatus cs _ _ = node_cons_status info
   lidS = sourceLogic cid
   lidT = targetLogic cid
 sig' <- coerceSign lid lidS "" sig
 (sig'',sen'') <- wrapMapTheory cid (plainSign sig', [])
 let
    gth = G_theory lidT (mkExtSign sig'') startSigId
                  (toThSens sen'') startThId
    labelM' = newInfoNodeLab
                  (extName "Freeness" $ dgn_name nodelab)
                  info
                  { node_origin = DGNormalForm n
                  , node_cons_status = mkConsStatus cs }
                  gth
    insM' = InsertNode (m', labelM')
 gMor <- gEmbedComorphism com (signOf s)
 let insE = InsertEdge (n,m', globDefLink gMor DGLinkProof)
     changeLabel = SetNodeLab nodelab
                  (n, nodelab{dgn_freenf = Just m', dgn_phi = Just gMor})
     newDG = changesDGH dg [insM', insE, changeLabel]
 return $ (m', changeDGH newDG $ SetNodeLab labelM' (m', labelM'
              { globalTheory = computeLabelTheory libEnv newDG
                               (m', labelM') }))

-- la translate node trebuie sa modific campurile dgn_freenf si dgn_phi
-- DONE
-- scriu theoremFreeShift

thmFreeShift :: DGRule
thmFreeShift = DGRule "TheoremFreeShift"

------------------------------------------------
-- Theorem free shift and  auxiliaries
-- moves theorem links to nodes with incoming free dfn links
-- to their freeness normal form (must be computed before)
-----------------------------------------------

theoremFreeShift :: LibName -> LibEnv -> Result LibEnv
theoremFreeShift ln  = return .
  Map.adjust (\ dg -> theoremFreeShiftAux (labNodesDG dg) dg) ln

-- | assume that the normal forms a commputed already.
-- return Nothing if nothing changed
theoremFreeShiftAux :: [LNode DGNodeLab] -> DGraph -> DGraph
theoremFreeShiftAux  ns dg = let
  nodesWFree = map fst $ filter
           (\ (_, lbl) -> labelHasFree lbl && isJust (dgn_freenf lbl)
           && isJust (dgn_phi lbl)) ns
     -- all nodes with incoming hiding links
     -- all the theorem links entering these nodes
     -- have to replaced by theorem links with the same origin
     -- but pointing to the normal form of the former target node
  ingoingEdges = concatMap (getInComingGlobalUnprovenEdges dg) nodesWFree
  in trace (show nodesWFree)$ foldl theoremFreeShiftForEdge
                              dg ingoingEdges

theoremFreeShiftForEdge :: DGraph -> LEdge DGLinkLab -> DGraph
theoremFreeShiftForEdge dg edge@(source, target, edgeLab) =
  case maybeResult $ theoremFreeShiftForEdgeAux dg edge of
   Nothing -> error "theoremFreeShiftForEdgeAux"
   Just (dg', pbasis) -> let
    provenEdge = (source, target, edgeLab
        { dgl_type = setProof (Proven thmFreeShift pbasis) $ dgl_type edgeLab
        , dgl_origin = DGLinkProof
        , dgl_id = defaultEdgeId })
    in insertDGLEdge provenEdge $ changeDGH dg' $ DeleteEdge edge

theoremFreeShiftForEdgeAux :: DGraph -> LEdge DGLinkLab
                           -> Result (DGraph, ProofBasis)
theoremFreeShiftForEdgeAux dg (sn, tn, llab) = do
  let tlab = labDG dg tn
      Just nfNode = dgn_freenf tlab
      phi = dgl_morphism llab
      Just muN = dgn_phi tlab
  let cmor1  = composeMorphisms phi muN
  case maybeResult cmor1 of
   Nothing -> error "composition"
   Just cmor -> do
    let newEdge =(sn, nfNode, defDGLink cmor globalThm DGLinkProof)
    case tryToGetEdge newEdge dg of
          Nothing -> let
           newGraph = changeDGH dg $ InsertEdge newEdge
           finalEdge = case getLastChange newGraph of
             InsertEdge final_e -> final_e
             _ -> error "Proofs.Global.globDecompForOneEdgeAux"
           in return
              (newGraph, addEdgeId emptyProofBasis $ getEdgeId finalEdge)
          Just e -> return (dg, addEdgeId emptyProofBasis $ getEdgeId e)

theoremFreeShiftFromList :: LibName -> [LNode DGNodeLab] -> LibEnv
                         -> Result LibEnv
theoremFreeShiftFromList ln ls =
  return . Map.adjust (theoremFreeShiftAux ls) ln


