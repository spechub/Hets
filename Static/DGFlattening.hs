{- |
Module      :  $Header$
Description :  Central datastructures for development graphs
Copyright   :  (c) Igor Stassiy, DFKI Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  i.stassiy@jacobs-university.de
Stability   :  provisional
Portability :  non-portable(Logic)


In this module we introduce flattening of the graph:
Flattening from level 1 to 0 - deleting all inclusion links,
and inserting a new node, with new computed theory (computeTheory).

Flattening from level 4 to 1 - deterimining renaming link,
inserting a new node with the renaming morphism applied to theory of a
source, deleting the link and setting a new inclusion link between a
new node and the target node.

In this module we introduce flattening of the graph. All the edges in the
graph are cut out and theories of a node with theories of all the incoming
nodes are merged into a theory of a new node and then inserted in the graph.
While the old nodes are deleted.
-}

module Static.DGFlattening (dg_flattening1,
                            libEnv_flattening1,
                            dg_flattening3,
                            libEnv_flattening3,
                            dg_flattening4,
                            libEnv_flattening4,
                            dg_flattening5,
                            libEnv_flattening5,
                            dg_flattening6,
                            libEnv_flattening6
                            ) where
import Logic.Grothendieck
import Logic.Logic
import Logic.Coerce
import Comorphisms.LogicGraph
import Static.DevGraph
import Static.GTheory
import Static.DevGraph
import Proofs.EdgeUtils
import Proofs.TheoremHideShift
import Propositional.Sign()
import Syntax.AS_Library
import Common.Result
import Common.ExtSign
import Data.Graph.Inductive.Graph hiding (empty)
import Data.Map hiding (intersection,empty)
import Data.Set hiding (intersection,insert)
import Data.List(tails)
import Data.Maybe(fromJust)
import qualified Data.Map as Map
import Control.Monad

dg_flattening1 :: LibEnv -> LIB_NAME -> Result DGraph
dg_flattening1 libEnv ln = do
 let
  dg = lookupDGraph ln libEnv
  nds =  nodesDG dg
  l_edges = labEdgesDG dg
  change_de =  Prelude.map (\ x -> DeleteEdge(x)) l_edges
  rule_e = replicate (length l_edges) FlatteningOne
  hist = [(rule_e
          ,change_de)]
  -- part for dealing with the graph itself
  updLib = updateLib libEnv ln nds
 return $ applyProofHistory hist (lookupDGraph ln updLib)
  where
   delLEdgesDG :: [LEdge DGLinkLab] -> DGraph -> DGraph
   delLEdgesDG ed dg = case ed of
    [] -> dg
    hd : tl -> delLEdgesDG tl ( delLEdgeDG hd dg )

   updateNodes :: LibEnv
                  -> LIB_NAME
                  -> DGraph
                  -> Node
                  -> Result (LIB_NAME, DGChange)
   updateNodes lib_Env l_n g n =
    let
     labRf = labDG g n
     lib_nd = lookupInRefNodesDG n g
      -- have to consider references here. computeTheory is applied
      -- to the node at the end of the chain of references only.
    in
     case lib_nd of
      Just (lib,nd) -> do
           updateNodes lib_Env lib g nd
      _ -> do
           (_,ndgn_theory) <- computeTheory False lib_Env l_n n
           return $(l_n,
                    SetNodeLab labRf (n,
                    labRf {dgn_theory = ndgn_theory}))

   updateLib :: LibEnv -> LIB_NAME -> [Node] -> LibEnv
   updateLib lib_Env l_n nds =
    case nds of
     [] ->  lib_Env
     hd:tl -> let
               g = lookupDGraph l_n lib_Env
               (l_name,change) = propagateErrors (updateNodes lib_Env
                                                              l_n
                                                              g
                                                              hd)
               refg = lookupDGraph l_name lib_Env
               new_dg = applyProofHistory [([FlatteningOne], [change])]
                                          refg
              in
               updateLib (insert l_name new_dg lib_Env) l_name tl


libEnv_flattening1 :: LibEnv -> Result LibEnv
libEnv_flattening1 lib = do
        new_lib_env <- mapM (\ (x,_) -> do
                         z <- dg_flattening1 lib x
                         return (x, z)) $ Map.toList lib
        return $ Map.fromList new_lib_env

dg_flattening4 :: LibEnv -> LIB_NAME -> DGraph
dg_flattening4 lib_Env l_n =
  let
   dg = lookupDGraph l_n lib_Env
   l_edges = labEdgesDG dg
   renamings = Prelude.filter (\ (_,_,x) -> let
                                    l_type = getRealDGLinkType x
                                  in
                                    case l_type of
                                     GlobalDefNoInc -> True
                                     _ -> False ) l_edges
   (fin_dg,ruls, chngs) = applyUpdDG renamings [] [] dg
  -- no need to care abput references as each node
  -- is preserved during flattening.
  in
   setProofHistoryDG [(ruls,chngs)] fin_dg
    where
     updateDGWithChanges :: (LEdge DGLinkLab)
                            -> DGraph
                            -> (DGraph,[DGChange])
     updateDGWithChanges l_edg@( v1, v2, label) d_graph =
      let
      --update nodes
       lv1 = labDG d_graph v1 
       lv2 = labDG d_graph v2 
       name = dgn_name lv1
       n_node = getNewNodeDG d_graph
       nlv1 = (do
                ( _, n_dgn_theory ) <- computeTheory True lib_Env l_n v1
                return $ lv1 {dgn_theory = n_dgn_theory } )
       nlv2 = (do
                ( _, n_dgn_theory ) <- computeTheory True lib_Env l_n v2
                return $ lv2 {dgn_theory = n_dgn_theory } )
       n_lnode = (do
             t_dgn_theory <-
              translateG_theory (dgl_morphism label)
                                (dgn_theory $ propagateErrors nlv1)
             return (n_node,
                     (newInfoNodeLab (name)
                                     (newNodeInfo DGFlattening)
                                     t_dgn_theory) ) )
       --create edge
       sign_source = signOf . dgn_theory . snd $ propagateErrors n_lnode
       sign_target = signOf . dgn_theory $ labDG d_graph v2
       n_edg = (do
                 ng_morphism <- ginclusion logicGraph
                                           sign_source
                                           sign_target
                 return (n_node,
                         v2,
                         label { dgl_morphism = ng_morphism,
                                 dgl_type = LocalDef ,
                                 dgl_origin = DGLinkFlatteningFour,
                                 dgl_id = defaultEdgeId }) )
       change_dg = [SetNodeLab lv1 (v1, propagateErrors nlv1 ),
                    SetNodeLab lv2 (v2, propagateErrors nlv2 ),
                    DeleteEdge(l_edg),
                    InsertNode(propagateErrors  n_lnode),
                    InsertEdge(propagateErrors n_edg)]
      in
       updateDGAndChanges d_graph change_dg

     applyUpdDG :: [LEdge DGLinkLab]
                         -> [DGRule]
                         -> [DGChange]
                         ->  DGraph
                         -> (DGraph,[DGRule],[DGChange])
     applyUpdDG l_list rl_l ch_l d_g = case l_list of
      [] -> (d_g, rl_l, ch_l)
      hd:tl -> let
                (dev_g,changes) = updateDGWithChanges hd d_g
                rules = replicate 3 FlatteningFour
               in
                applyUpdDG tl
                           (rl_l ++ rules)
                           (ch_l ++ changes)
                           dev_g

libEnv_flattening4 :: LibEnv -> Result LibEnv
libEnv_flattening4 libEnvi =
       let
        new_lib_env = Prelude.map (\ (x,_) -> 
                        let
                         z = dg_flattening4 libEnvi x
                        in
                         (x, z)) $ Map.toList libEnvi
       in
        return $ Map.fromList new_lib_env


dg_flattening5 :: LibEnv -> LIB_NAME -> DGraph
dg_flattening5 lib_Envir lib_name =
  let
   dg = lookupDGraph lib_name lib_Envir
   nods = nodesDG dg
   nf_dg = applyUpdNf lib_Envir lib_name dg nods
   l_edges = labEdgesDG nf_dg
   hids = Prelude.filter (\ (_,_,x) -> (case dgl_type x of
                                         HidingDef -> True
                                         _ -> False)) l_edges
   dhid_rule = replicate (length hids) FlatteningFive
   dhid_change = Prelude.map (\ x -> DeleteEdge(x)) hids
   old_hist = proofHistory dg
   nfHist = proofHistory nf_dg
   dhid_hist=  (take (length nfHist - length old_hist) nfHist)
                 ++ [(dhid_rule, dhid_change)]
  -- no need to care about references either, as nodes are preserved
  -- after flattening, as well as references.
  in
   (applyProofHistory dhid_hist dg)
     where 
      applyUpdNf :: LibEnv 
                    -> LIB_NAME
                    -> DGraph
                    -> [Node]
                    -> DGraph
      applyUpdNf lib_Envi lib_Name dg l_nodes =
       case l_nodes of
        [] ->  dg
        hd:tl -> let
          new_Lib = propagateErrors $ convertToNf lib_Name
                                                  lib_Envi
                                                  hd
          new_dg = lookupDGraph lib_Name new_Lib
         in
          applyUpdNf new_Lib lib_Name new_dg tl

libEnv_flattening5 :: LibEnv -> Result LibEnv
libEnv_flattening5 libEnvi =
 let
  new_lib_env = Prelude.map (\ (x,_) -> 
       let
        z = dg_flattening5 libEnvi x
       in
        (x, z)) $ Map.toList libEnvi
 in
  return $ Map.fromList new_lib_env

dg_flattening6 :: LibEnv -> LIB_NAME -> Result DGraph
dg_flattening6 libEnv ln = do
 let
  dg = lookupDGraph ln libEnv
  l_edges = labEdgesDG dg
  nds = nodesDG dg
  het_comorph = Prelude.filter (\ (_,_,x) -> 
                 let
                  comorph = dgl_morphism x
                 in
                  (not $ isHomogeneous comorph)) l_edges
  het_rules = replicate (length het_comorph) FlatteningSix 
  het_del_changes = Prelude.map (\x -> DeleteEdge(x)) l_edges
  updLib = updateLib libEnv ln nds
  all_hist = [(het_rules , het_del_changes)]
 return $ applyProofHistory all_hist (lookupDGraph ln updLib)
  where
   updateNodes :: LibEnv
                  -> LIB_NAME
                  -> DGraph
                  -> Node
                  -> Result (LIB_NAME, DGChange)
   updateNodes lib_Env l_n g n =
    let
     labRf = labDG g n
     lib_nd = lookupInRefNodesDG n g
     -- have to consider references here. computeTheory is applied to the
     -- node at the end of the chain of references only.
    in
     case lib_nd of
      Just (lib,nd) -> do
       updateNodes lib_Env lib g nd
      _ -> do
       (_,ndgn_theory) <- computeTheory False lib_Env l_n n
       return $(l_n,
                SetNodeLab labRf (n,
                labRf {dgn_theory = ndgn_theory}))

   updateLib :: LibEnv -> LIB_NAME -> [Node] -> LibEnv
   updateLib lib_Env l_n nds =
    case nds of
     [] ->  lib_Env
     hd:tl -> let
        g = lookupDGraph l_n lib_Env
        (l_name,change) = propagateErrors (updateNodes lib_Env l_n g hd)
        refg = lookupDGraph l_name lib_Env
        new_dg = applyProofHistory [([FlatteningOne], [change])] refg
       in
        updateLib (insert l_name new_dg libEnv) l_name tl

libEnv_flattening6 :: LibEnv -> Result LibEnv
libEnv_flattening6 lib = do
 new_lib_env <- mapM (\ (x,_) -> do
         z <- dg_flattening6 lib x
         return (x, z)) $ Map.toList lib
 return $ Map.fromList new_lib_env

dg_flattening3 :: LibEnv -> LIB_NAME -> Result DGraph
dg_flattening3 libEnv ln = do
let
 dg = lookupDGraph ln libEnv
 all_nodes = nodesDG dg
 imp_nds = Prelude.filter (\ x -> ( length (innDG dg x) > 1)) all_nodes
 -- as previously, no need to care about reference nodes,
 -- as previous one remain same.
return (applyUpdateAllLevels dg imp_nds)
 where
 -- get intersection of list of G_sign with time complexity log(n).
 getIntersectionOfAll :: [G_sign] -> [G_sign] -> Result G_sign
 getIntersectionOfAll signs n_signs =
  case signs of
   [] -> case n_signs of
    [] -> error "empty signature"
    hd:[] -> return hd
    hd:tl -> getIntersectionOfAll (hd:tl) []

   hd@(G_sign lid1 extSign1 _)
    :[] -> case n_signs of
      [] -> return hd
      (G_sign lid2 (ExtSign signtr2 _) _)
       :[] -> do
         (ExtSign sign1 _) <- coerceSign lid1
                                         lid2
                                         "getIntersectionOfAll"
                                         extSign1
         n_sign <- intersection lid2
                                sign1
                                signtr2
         return $ G_sign lid2 (ExtSign n_sign empty) startSigId
      hd1:tl1 -> getIntersectionOfAll (hd:hd1:tl1) []

   (G_sign lid1 extSign1 _)
    :(G_sign lid2 (ExtSign signtr2 _) _)
    :tl -> let
          n_signtr = propagateErrors (do
          (ExtSign sign1 _) <- coerceSign lid1
                                          lid2
                                          "getIntersectionOfAll"
                                          extSign1
          n_sign <- intersection lid2 sign1 signtr2
          return $ G_sign lid2 (ExtSign n_sign empty) startSigId)
         in
          getIntersectionOfAll tl (n_signtr:n_signs)
 getAllCombinations :: Int -> [Node] -> [[Node]]
 getAllCombinations 0 _  = [ [] ]
 getAllCombinations n xs = [ y:ys | y:xs' <- tails xs
                              , ys <- getAllCombinations (n-1) xs']

 getAllSignatures :: DGraph -> Int -> [Node] -> [([Node],G_sign)]
 getAllSignatures _ 0 _ = []
 getAllSignatures dg n xs = let
   combs = getAllCombinations n xs
   signs = Prelude.map (\ x ->
                         (x,Prelude.map (\ y ->
                          signOf $ dgn_theory (labDG dg y)) x)) combs
   nemt_sign_map = Prelude.map (\ (x,y) ->
                         (x,propagateErrors $ getIntersectionOfAll y []))
  in
   Prelude.filter (\ (_,y@(G_sign lid _  _)) ->
                    not (y==(emptyG_sign $ fromJust $ data_logic lid))
                                               ) (nemt_sign_map signs)

 createLinks :: DGraph -> (LNode DGNodeLab) -> [Node] -> [LEdge DGLinkLab]
 createLinks _ _ [] = []
 createLinks dg (nd,lb) (hd:tl) =
  let
   sign_source = signOf  (dgn_theory lb)
   sign_target = signOf (dgn_theory $ labDG dg hd)
   n_edg = (do
             ng_morphism <- ginclusion logicGraph sign_source sign_target
             return (nd, hd, DGLink { dgl_morphism = ng_morphism,
                                      dgl_type = LocalDef,
                                      dgl_origin = DGLinkFlatteningThree,
                                      dgl_id = defaultEdgeId }))
  in
   (propagateErrors n_edg) : createLinks dg (nd,lb) tl

 insertLinksAndNodes ::  DGraph
                         -> [([Node],G_sign)]
                         -> [DGChange]
                         -> (DGraph,[DGChange])
 insertLinksAndNodes dg list chngs = case list of
  [] -> (dg,chngs)
  (nds, G_sign lid sign ind):tl -> let
    n_nd = getNewNodeDG dg
    n_theory = noSensGTheory lid sign ind
    n_name = dgn_name $ labDG dg (head nds)
    n_info = newNodeInfo DGFlattening
    n_lab = newInfoNodeLab n_name n_info n_theory
    n_nd_change = InsertNode((n_nd,n_lab))
    n_ed_change = Prelude.map (\ x
                                -> InsertEdge(x)) (createLinks dg
                                                               (n_nd,n_lab)
                                                               nds)
    (n_dg,n_chngs) = updateDGAndChanges dg (n_ed_change ++ [n_nd_change])
   in
    insertLinksAndNodes n_dg tl (n_chngs++chngs)

 -- gives the new graph in case old one is updated and nothing if is not.
 updateLevelHist :: DGraph -> [Node] -> Int -> Maybe DGraph
 updateLevelHist dg nds n = let
   signs = getAllSignatures dg n nds
   (n_dg,n_chngs) = insertLinksAndNodes dg signs []
   n_rls = replicate (length n_chngs) FlatteningThree
  in
   case signs of
    [] -> Nothing
    _ ->  Just (applyProofHistory [(n_rls,n_chngs)] n_dg)

 updateAllLevels :: DGraph -> [Node] -> Int -> DGraph
 updateAllLevels dg nds n =
  let
   smth = updateLevelHist dg nds n
  in
   case smth of
    Nothing -> dg
    Just smth ->  case (n<(length nds)+1) of
            True -> updateAllLevels smth nds (n+1)
            False -> dg

 applyUpdateAllLevels :: DGraph -> [Node] -> DGraph
 applyUpdateAllLevels dg nds = case nds of
  [] -> dg
  hd:tl -> let
            inc_edgs = innDG dg hd
            inc_nds = Prelude.map (\ (x,_,_) -> x) inc_edgs
            n_dg = updateAllLevels dg  inc_nds 2
           in
            applyUpdateAllLevels n_dg tl

libEnv_flattening3 :: LibEnv -> Result LibEnv
libEnv_flattening3 lib = do
 new_lib_env <- mapM (\ (x,_) -> do
         z <- dg_flattening3 lib x
         return (x, z)) $ Map.toList lib
 return $ Map.fromList new_lib_env