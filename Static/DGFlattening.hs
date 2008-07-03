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

module Static.DGFlattening (dg_flattening2,
                            libEnv_flattening2,
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
import Data.List(tails,elem)
import Data.Maybe(fromJust,isJust)
import qualified Data.Map as Map
import Control.Monad

dg_flattening2 :: LibEnv -> LIB_NAME -> Result DGraph
dg_flattening2 libEnv ln = do
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


libEnv_flattening2 :: LibEnv -> Result LibEnv
libEnv_flattening2 lib = do
        new_lib_env <- mapM (\ (x,_) -> do
                         z <- dg_flattening2 lib x
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
return  $ applyToAllNodes dg imp_nds
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
 -- tells if two lists are equal or one contained in the other
 containedInList :: [Node] -> [Node] -> Bool
 containedInList [] _ = True
 containedInList (hd:tl) l2 = if elem hd l2 then containedInList tl l2
                               else False

 -- get the tripple with corresponding lists of nodes being equal
 getInList :: [Node] -> [([Node],Node,G_sign)] -> Maybe ([Node],Node,G_sign)
 getInList _ [] = Nothing
 getInList l (trpl@(nds,_,_):tl) = if containedInList l nds then Just trpl
                                        else getInList l tl
 -- takes initial nodes, one level and gives out 
 searchThroughSigns :: [Node]
                       -> [([Node],Node,G_sign)]
                       -> Maybe ([Node],G_sign)
 searchThroughSigns l@(hd1:hd2:tl) trpls = case getInList (hd1:tl) trpls of
  Nothing -> Nothing
  Just (_,_,gsig1@(G_sign lid _ _)) ->
     case getInList (hd2:tl) trpls of
         Nothing -> Nothing
         Just (_,_,gsig2) ->
            let
             n_sig =  propagateErrors (getIntersectionOfAll [gsig1,gsig2] [])
            in
             case n_sig == (emptyG_sign (Logic lid)) of
              True -> Nothing
              False -> Just (l, n_sig)
 -- for some level, get the next level with the signatures for each node computed
 getAllSignatures :: DGraph
                     -> [Node]
                     -> [([Node],Node,G_sign)]
                     -> Int
                     -> [([Node],G_sign)]
 getAllSignatures _ _ _ 0 = []
 getAllSignatures _ nds trpls n =  --dg
  let
   combs = getAllCombinations n nds
  in
   Prelude.map (\ x -> fromJust x) $
      Prelude.filter (\ x -> isJust x)
         (Prelude.map (\ x -> searchThroughSigns x trpls) combs)

 -- attach new nodes to the level
 attachNewNodes :: [([Node],G_sign)] -> Int -> [([Node],Node,G_sign)]
 attachNewNodes [] _ = []
 attachNewNodes ((hd,sg):tl) n = (hd,n,sg):(attachNewNodes tl (n+1))

 -- for a specific nodelab and list of nodes,
 -- create links between node and list of nodes.
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

 -- for two levels given, give out a node with it's g_sign in upper level and
 -- list of nodes from the lower one, to which it should be connected with a link.
 searchThroughLinks :: [([Node],Node,G_sign)] -- previous level
                       -> [([Node],Node,G_sign)] -- current level
                       -> [(Node,[Node],G_sign)]
 searchThroughLinks l1 l2 = case l2 of
  [] -> []
  (nds,nd,sig):tl -> case l1 of
        [] -> []
        _ -> let
               fltrd = Prelude.filter (\(y,_,_) -> containedInList nds y) l2
               nods = Prelude.map (\ (_,x,_) -> x) fltrd
             in
               (nd,nods,sig):searchThroughLinks l1 tl

 -- given graph and two levels, insert new links between those two levels.
 insertLinksAndNodes ::  DGraph
                         -> [Node]                 -- initial nodes
                         -> [([Node],Node,G_sign)] -- previous level
                         -> [([Node],Node,G_sign)] -- current level
                         -> DGraph
 insertLinksAndNodes dg nds list1 list2 = case list2 of
  [] -> dg
  _ -> let
        ls = searchThroughLinks list1 list2
       in case ls of
        [] -> dg
        _  -> let
           chngs = Prelude.map (\ (x,
                                   y,
                                   G_sign lid (ExtSign sign symb) ind) -> let
             n_theory = noSensGTheory lid (ExtSign sign symb) ind
             n_name = dgn_name $ labDG dg (head nds)
             n_info = newNodeInfo DGFlattening
             n_lab = newInfoNodeLab n_name n_info n_theory
             n_nd_change = InsertNode((x,n_lab))
            in
             [n_nd_change]++(Prelude.map (\ z ->
                                     InsertEdge(z)) (createLinks dg (x,n_lab)
                                                                    y))) ls
           (n_dg,n_chngs) = updateDGAndChanges dg (concat chngs)
           rls = replicate (length n_chngs) FlatteningThree
          in
           applyProofHistory [(rls,n_chngs)] n_dg

 -- repeat the procedure above for all levels.
 fromLevelToLevel ::  DGraph
                      -> [Node]
                      -> [([Node],Node,G_sign)]
                      -> Int
                      -> (DGraph,[Node],[([Node],Node,G_sign)],Int)
 fromLevelToLevel dg nds tripls n = case (length nds) of
  2 -> let
        signx = signOf $ dgn_theory (labDG dg (head nds))
        signy = signOf $ dgn_theory (labDG dg (head $ tail nds))
        n_sign = propagateErrors $ getIntersectionOfAll [signx,signy] []
        init_atchd = attachNewNodes [(nds,n_sign)] (getNewNodeDG dg)
        chngs = Prelude.map (\ (x,y,G_sign lid (ExtSign sign symb) ind) -> let
             n_theory = noSensGTheory lid (ExtSign sign symb) ind
             n_name = dgn_name $ labDG dg (head nds)
             n_info = newNodeInfo DGFlattening
             n_lab = newInfoNodeLab n_name n_info n_theory
             n_nd_change = InsertNode((y,n_lab))
            in
             [n_nd_change]++(Prelude.map (\ z -> InsertEdge(z)) (createLinks dg (y,n_lab) x))) init_atchd
        (n_dg,n_chngs) = updateDGAndChanges dg (concat chngs)
        rls = replicate (length n_chngs) FlatteningThree
        nn_dg = applyProofHistory [(rls, n_chngs)] n_dg
       in
        (nn_dg,[],[],0)
  _ -> case tripls of
        [] -> (dg,[],[],0)
        _  ->
            let
             signs = getAllSignatures dg nds tripls n
             atchd = attachNewNodes signs (getNewNodeDG dg)
             n_dg = insertLinksAndNodes dg nds tripls atchd
            in
             case (n-(length nds)) of
              1 -> (dg,nds,[],0)
              _  -> fromLevelToLevel n_dg nds atchd (n+1)

 -- update all levels, firstly precomputing the initial level.
 updateAllLevels :: DGraph -> [Node] -> DGraph
 updateAllLevels dg nds =
  let
   init_comb = getAllCombinations 2 nds
   init_signs = Prelude.filter (\ ([_,_],z@(G_sign lid _ _)) ->
                                    z == (emptyG_sign (Logic lid)))
                                      (Prelude.map (\ [x,y] -> let
                                         signx = signOf $ dgn_theory (labDG dg x)
                                         signy = signOf $ dgn_theory (labDG dg y)
                                         n_sign = getIntersectionOfAll [signx
                                                                       ,signy] []
                                        in
                                         ([x,y],propagateErrors n_sign)) init_comb)
   init_atchd = attachNewNodes init_signs (getNewNodeDG dg)
   (n_dg,_,_,_) = fromLevelToLevel dg nds init_atchd 3
  in
   n_dg

 -- apply updating to all nodes in the graph.
 applyToAllNodes :: DGraph -> [Node] -> DGraph
 applyToAllNodes dg nds = case nds of
  [] -> dg
  hd:tl -> let
            in_nds = Prelude.map (\ (x,_,_) -> x) (innDG dg hd)
            n_dg = updateAllLevels dg in_nds
           in 
            applyToAllNodes n_dg tl

libEnv_flattening3 :: LibEnv -> Result LibEnv
libEnv_flattening3 lib = do
 new_lib_env <- mapM (\ (x,_) -> do
         z <- dg_flattening3 lib x
         return (x, z)) $ Map.toList lib
 return $ Map.fromList new_lib_env