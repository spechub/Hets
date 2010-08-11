{- |
Module      :  $Header$
Description :  normalization of freeness
Copyright   :  (c) Mihai Codescu, DFKI GmbH 2010
License     :  GPLv2 or higher

Maintainer  :  Mihai.Codescu@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

compute normal forms
-}

module Proofs.Freeness
    ( freeness
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
import Static.History

import Common.ExtSign
import Common.LibName
import Common.Result

import Data.Graph.Inductive.Graph as Graph
import qualified Data.Map as Map
import Control.Monad

import Data.List(nub)
import Common.Lib.Graph

freenessRule :: DGRule
freenessRule = DGRule "Freeness"

freeness :: LibName -> LibEnv -> Result LibEnv
freeness ln le = do
  let dg = lookupDGraph ln le
  newDg <- freenessDG le dg
  return $ Map.insert ln
    (groupHistory dg freenessRule newDg) le

freenessDG :: LibEnv -> DGraph -> Result DGraph
freenessDG le dgraph = do
 foldM (handleEdge le) dgraph $ labEdgesDG dgraph

handleEdge :: LibEnv -> DGraph ->  LEdge DGLinkLab -> Result DGraph
handleEdge libEnv dg edge@(m,n,x) = do
    case dgl_type x of
     FreeOrCofreeDefLink _ _ -> do
      let phi = dgl_morphism x
          mlab = labDG dg m
          gth= case globalTheory mlab of
                  Nothing -> dgn_theory $ labDG dg m
                  Just t -> t
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
                   (extName "Freeness" $ dgn_name nodelab)
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
                succs = map (\y -> (y,labDG dg y)) $ descs (dgBody dg) n
                labCh =  [SetNodeLab labelK (k, labelK
                          { globalTheory = computeLabelTheory libEnv newDG
                               (k, labelK) }),
                         SetNodeLab labelN (n, labelN
                          { globalTheory = computeLabelTheory libEnv newDG
                               (n, labelN)
                            , labelHasHiding = True })
                         ] ++
                         map (\(y,ly) -> SetNodeLab ly
                                         (y, ly{labelHasHiding = True})) succs
            return $ changesDGH newDG $ labCh
           _ -> return dg
              --  do
              --  -- failed in logic lid, look for comorphism and translate
              --  -- then recursive call
              -- let look = lookupQTA_in_LG $ language_name lid
              -- case maybeResult look of
              --  Nothing -> return dg
              --     -- can't translate to a logic where qta is implemented
              --  Just com -> do
              --   (m', dgM) <- translateFree libEnv dg edge com
              --   foldM (handleEdge libEnv) dgM $ out (dgBody dgM) m'
     _ -> return dg

descs :: Gr a b -> Node -> [Node]
descs graph node = let
   d nList descList =
    case nList of
      [] -> descList
      _ -> let
             newDescs = concatMap (\x -> suc graph x) nList
             nList' = filter (\x -> not $ (x `elem` nList) ||
                                          (x `elem` descList))
                      newDescs
             descList' = nub $ descList ++ newDescs
           in d nList' descList'
 in d [node] []


-- translateFree :: LibEnv -> DGraph -> LEdge DGLinkLab -> AnyComorphism ->
--                  Result (Node, DGraph)
-- translateFree le dg edge@(m,n,x) com = do
--  (m', dg') <- translateNode le dg m (dgn_theory $ labDG dg m) com
--  (n', dg'') <- translateNode le dg' n (dgn_theory $ labDG dg n) com
--  dg''' <- translateEdge dg'' edge (dgl_morphism x) com m' n'
--  return (m', dg''')

-- translateEdge :: DGraph -> LEdge DGLinkLab -> GMorphism -> AnyComorphism ->
--               Node -> Node -> Result DGraph
-- translateEdge dg _edge (GMorphism cid _sig _i1 mor1 _i2)
--               (Comorphism cid') m n = do
--  let
--   lidS = sourceLogic cid'
--   lidT = targetLogic cid'
--  mor2 <- coerceMorphism (targetLogic cid) lidS "" mor1
--  mor3 <- map_morphism cid' mor2
--  let
--    gm = gEmbed $ mkG_morphism lidT mor3
--    --del = DeleteEdge edge
--    edge' = defDGLink gm
--              (FreeOrCofreeDefLink Free $ EmptyNode $ Logic lidT)  DGLinkProof
--    ins = InsertEdge (m, n, edge')
--  return $ changesDGH dg  [ins]

-- translateNode :: LibEnv -> DGraph -> Node -> G_theory -> AnyComorphism ->
--                  Result (Node, DGraph)
-- translateNode libEnv dg n s@(G_theory lid sig _ _ _) com@(Comorphism cid) = do
--  let
--    m' = getNewNodeDG dg -- new node
--    nodelab = labDG dg n
--    info = nodeInfo nodelab
--    ConsStatus cs _ _ = node_cons_status info
--    lidS = sourceLogic cid
--    lidT = targetLogic cid
--  sig' <- coerceSign lid lidS "" sig
--  (sig'',sen'') <- wrapMapTheory cid (plainSign sig', [])
--  let
--     gth = G_theory lidT (mkExtSign sig'') startSigId
--                   (toThSens sen'') startThId
--     labelM' = newInfoNodeLab
--                   (extName "Freeness" $ dgn_name nodelab)
--                   info
--                   { node_origin = DGNormalForm n
--                   , node_cons_status = mkConsStatus cs }
--                   gth
--     insM' = InsertNode (m', labelM')
--  gMor <- gEmbedComorphism com (signOf s)
--  let insE = InsertEdge (n,m', globDefLink gMor DGLinkProof)
--      changeLabel = SetNodeLab nodelab
--                   (n, nodelab{dgn_freenf = Just m', dgn_phi = Just gMor})
--      newDG = changesDGH dg [insM', insE, changeLabel]
--  return $ (m', changeDGH newDG $ SetNodeLab labelM' (m', labelM'
--               { globalTheory = computeLabelTheory libEnv newDG
--                                (m', labelM') }))

-- thmFreeShift :: DGRule
-- thmFreeShift = DGRule "TheoremFreeShift"

------------------------------------------------
-- Theorem free shift and  auxiliaries
-- moves theorem links to nodes with incoming free dfn links
-- to their freeness normal form (must be computed before)
-----------------------------------------------

-- theoremFreeShift :: LibName -> LibEnv -> Result LibEnv
-- theoremFreeShift ln  = return .
--   Map.adjust (\ dg -> theoremFreeShiftAux (labNodesDG dg) dg) ln

-- -- | assume that the normal forms a commputed already.
-- -- return Nothing if nothing changed
-- theoremFreeShiftAux :: [LNode DGNodeLab] -> DGraph -> DGraph
-- theoremFreeShiftAux  ns dg = let
--   nodesWFree = map fst $ filter
--            (\ (_, lbl) -> labelHasFree lbl && isJust (dgn_freenf lbl)
--            && isJust (dgn_phi lbl)) ns
--      -- all nodes with incoming hiding links
--      -- all the theorem links entering these nodes
--      -- have to replaced by theorem links with the same origin
--      -- but pointing to the normal form of the former target node
--   ingoingEdges = concatMap (getInComingGlobalUnprovenEdges dg) nodesWFree
--   in foldl theoremFreeShiftForEdge
--                               dg ingoingEdges

-- theoremFreeShiftForEdge :: DGraph -> LEdge DGLinkLab -> DGraph
-- theoremFreeShiftForEdge dg edge@(source, target, edgeLab) =
--   case maybeResult $ theoremFreeShiftForEdgeAux dg edge of
--    Nothing -> error "theoremFreeShiftForEdgeAux"
--    Just (dg', pbasis) -> let
--     provenEdge = (source, target, edgeLab
--         { dgl_type = setProof (Proven thmFreeShift pbasis) $ dgl_type edgeLab
--         , dgl_origin = DGLinkProof
--         , dgl_id = defaultEdgeId })
--     in insertDGLEdge provenEdge $ changeDGH dg' $ DeleteEdge edge

-- theoremFreeShiftForEdgeAux :: DGraph -> LEdge DGLinkLab
--                            -> Result (DGraph, ProofBasis)
-- theoremFreeShiftForEdgeAux dg (sn, tn, llab) = do
--   let tlab = labDG dg tn
--       Just nfNode = dgn_freenf tlab
--       phi = dgl_morphism llab
--       Just muN = dgn_phi tlab
--   let cmor1  = composeMorphisms phi muN
--   case maybeResult cmor1 of
--    Nothing -> error "composition"
--    Just cmor -> do
--     let newEdge =(sn, nfNode, defDGLink cmor globalThm DGLinkProof)
--     case tryToGetEdge newEdge dg of
--           Nothing -> let
--            newGraph = changeDGH dg $ InsertEdge newEdge
--            finalEdge = case getLastChange newGraph of
--              InsertEdge final_e -> final_e
--              _ -> error "Proofs.Global.globDecompForOneEdgeAux"
--            in return
--               (newGraph, addEdgeId emptyProofBasis $ getEdgeId finalEdge)
--           Just e -> return (dg, addEdgeId emptyProofBasis $ getEdgeId e)

-- theoremFreeShiftFromList :: LibName -> [LNode DGNodeLab] -> LibEnv
--                          -> Result LibEnv
-- theoremFreeShiftFromList ln ls =
--   return . Map.adjust (theoremFreeShiftAux ls) ln
