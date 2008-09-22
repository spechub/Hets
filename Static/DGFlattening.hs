{- |
Module      :  $Header$
Description :  Central datastructures for development graphs
Copyright   :  (c) Igor Stassiy, DFKI Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  i.stassiy@jacobs-university.de
Stability   :  provisional
Portability :  non-portable(Logic)


In this module we introduce flattening of the graph:

Flattening importings - deleting all inclusion links,
 and inserting a new node, with new computed theory (computeTheory).

Flattening disjoint unions - for each node with more than two importings
 modify importings in such a way that at each level, only disjoint signatures
 are imported.

Flattening renaming - deterimining renaming link,
inserting a new node with the renaming morphism applied to theory of a
source, deleting the link and setting a new inclusion link between a
new node and the target node.

Flattening hiding links - for each compute normal form if there is such
 and eliminate hiding links.

Flattening heterogeneity - for each heterogeneous link, compute theory of
 a target node and eliminate heterogeneous link.

-}

module Static.DGFlattening (dg_flattening2,
                            libEnv_flattening2,  -- importing
                            dg_flattening3,
                            libEnv_flattening3,  -- disjoint unions
                            dg_flattening4,
                            libEnv_flattening4,  -- import with renaming
                            dg_flattening5,
                            libEnv_flattening5,  -- hiding
                            dg_flattening6,
                            libEnv_flattening6   -- heterogeneity
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

import Common.ExtSign
import Common.Id
import Common.LibName
import Common.Result

import Data.Graph.Inductive.Graph
import Data.List (tails)
import Data.Maybe (catMaybes)
import qualified Data.Map as Map
import Control.Monad

unzipProofHistory :: ProofHistory -> ProofHistory
unzipProofHistory ph =
      let
        chngs = concatMap snd ph
        rls = concatMap fst ph
       in
        [(rls,chngs)]

dg_flattening2 :: LibEnv -> LIB_NAME -> Result DGraph
dg_flattening2 libEnv ln = do
 let
  dg = lookupDGraph ln libEnv
  nds =  nodesDG dg
  -- part for dealing with the graph itself
  updLib = updateLib libEnv ln nds
  updDG =  lookupDGraph ln updLib
  l_edges = labEdgesDG updDG
  change_de =  map (\ x -> DeleteEdge(x)) l_edges
  rules_de = replicate (length l_edges) FlatteningOne
  hist_de = [(rules_de
             ,change_de)]
  n_hist = proofHistory updDG
  o_hist = proofHistory dg
  dif_hist = unzipProofHistory hist_de ++ (take (length n_hist -
                                                 length o_hist) n_hist)
  (n_dg,_) = updateDGAndChanges dg change_de
 return $ n_dg {proofHistory = dif_hist ++ o_hist}
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
               ref_dg = lookupDGraph l_name lib_Env
               (u_dg,u_change) = updateDGAndChanges ref_dg [change]
               new_dg = addToProofHistoryDG ([FlatteningOne], u_change)
                                            u_dg
              in
               updateLib (Map.insert l_name new_dg lib_Env) l_name tl


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
   renamings = filter (\ (_,_,x) -> let
                                    l_type = getRealDGLinkType x
                                  in
                                    case l_type of
                                     GlobalDefNoInc -> True
                                     _ -> False ) l_edges
   (fin_dg,ruls, chngs) = applyUpdDG renamings [] [] dg
  -- no need to care about references as each node
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
                                 dgl_type = GlobalDef ,
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
        new_lib_env = map (\ (x,_) ->
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
   l_edges = labEdgesDG dg
   hids = filter (\ (_,_,x) -> (case dgl_type x of
                                         HidingDef -> True
                                         _ -> False)) l_edges
   dhid_rule = replicate (length hids) FlatteningFive
   dhid_change = map (\ x -> DeleteEdge(x)) hids
   old_hist = proofHistory dg
   nfHist = proofHistory nf_dg
   dhid_hist = (take (length nfHist - length old_hist) nfHist)
                ++ [(dhid_rule, dhid_change)]
  -- no need to care about references either, as nodes are preserved
  -- after flattening, as well as references.
  in
   (applyProofHistory (unzipProofHistory dhid_hist) dg)
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
  new_lib_env = map (\ (x,_) ->
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
  het_comorph = filter (\ (_,_,x) ->
                 let
                  comorph = dgl_morphism x
                 in
                  (not $ isHomogeneous comorph)) l_edges
  het_rules = replicate (length het_comorph) FlatteningSix
  het_del_changes = map (\x -> DeleteEdge(x)) het_comorph
  updLib = updateNodes libEnv ln nds
  all_hist = [(het_rules , het_del_changes)]
 return $ applyProofHistory all_hist (lookupDGraph ln updLib)
  where
   lookUpReferenceChain :: LibEnv -> LIB_NAME -> Node -> (LIB_NAME,Node)
   lookUpReferenceChain lib_Env libName nd =
    case (lookupInRefNodesDG nd (lookupDGraph libName lib_Env)) of
     Just (n_lib,n_nd) -> lookUpReferenceChain lib_Env n_lib n_nd
     Nothing -> (libName,nd)

   updateNodes :: LibEnv
                  -> LIB_NAME
                  -> [Node]
                  -> LibEnv
   updateNodes lib_Env l_n nds = case nds of
    [] -> lib_Env
    hd:tl -> let
      -- have to consider references here. computeTheory is applied to the
      -- node at the end of the chain of references only.
      (lname,nd) = lookUpReferenceChain lib_Env l_n hd
      labRf = labDG (lookupDGraph lname lib_Env) nd
      change = (do (_,ndgn_theory) <- computeTheory False lib_Env lname nd
                   return $ SetNodeLab labRf
                                       (nd,
                                        labRf {dgn_theory = ndgn_theory}))
      n_dg = applyProofHistory [([FlatteningSix],
                                 [propagateErrors change])]
                               (lookupDGraph lname lib_Env)
     in
      (updateNodes (Map.insert lname n_dg lib_Env) l_n tl)

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
 imp_nds = filter (\ x -> ( length (innDG dg x) > 1)) all_nodes
 -- as previously, no need to care about reference nodes,
 -- as previous one remain same.
return $ applyToAllNodes dg imp_nds
 where

 getIntersectionOfAll :: [G_sign] -> Result G_sign
 getIntersectionOfAll signs =
  case signs of
   [] -> error "empty signatures list"

   hd:[] -> return hd

   (G_sign lid1 extSign1 _)
    :(G_sign lid2 (ExtSign signtr2 _) _)
    :tl -> let
            n_signtr = propagateErrors (do
               (ExtSign sign1 _) <- coerceSign lid1
                                               lid2
                                               "getIntersectionOfAll"
                                               extSign1
               n_sign <- intersection lid2 sign1 signtr2
               return $ G_sign lid2 (mkExtSign n_sign) startSigId)
           in
            case  (n_signtr) == (emptyG_sign (Logic lid2)) of
             True -> return n_signtr
             False -> getIntersectionOfAll (n_signtr:tl)

 getAllCombinations :: Int -> [Node] -> [[Node]]
 getAllCombinations 0 _  = [ [] ]
 getAllCombinations n xs = [ y:ys | y:xs' <- tails xs
                           , ys <- getAllCombinations (n-1) xs']
 -- tells if two lists are equal or one contained in the other
 containedInList :: [Node] -> [Node] -> Bool
 containedInList [] _ = True
 containedInList (hd:tl) l2 = if elem hd l2 then containedInList tl l2
                               else False

 -- attach new nodes to the level
 attachNewNodes :: [([Node],G_sign)] -> Int -> [([Node],Node,G_sign)]
 attachNewNodes [] _ = []
 attachNewNodes ((hd,sg):tl) n = (hd,n,sg):(attachNewNodes tl (n+1))

 -- search for a match for a given combination in a level
 searchForMatch :: [Node]
                   -> [([Node],Node,G_sign)]
                   -> Maybe ([Node],Node,G_sign)
 searchForMatch _ [] = Nothing
 searchForMatch l ((tripl@(nds,_,_)):tl) = if containedInList l nds
                                              then Just tripl
                                                   else searchForMatch l tl

 -- take a combination of nodes, previous level,
 -- and get the signature for the next level
 matchCombinations :: [Node]
                       -> [([Node],Node,G_sign)]
                       -> Maybe ([Node],G_sign)
 matchCombinations []  _ = Nothing
 matchCombinations (_:[]) _= Nothing
 matchCombinations l@(hd1:hd2:tl) trpls =
  case searchForMatch (hd1:tl) trpls of
   Nothing -> Nothing
   Just (_,_,gsig1@(G_sign lid _ _)) ->
     case searchForMatch (hd2:tl) trpls of
         Nothing -> Nothing
         Just (_,_,gsig2) ->
            let
             n_sig =  propagateErrors (getIntersectionOfAll [gsig1,gsig2])
            in
             case n_sig == (emptyG_sign (Logic lid)) of
              True ->  Nothing
              False -> Just (l, n_sig)

 -- for a dg and a level, create labels for the new nodes
 createLabels :: DGraph
                 -> [([Node],Node,G_sign)]
                 -> Result [LNode DGNodeLab]
 createLabels dg tripls = case tripls of
  [] -> error "createLabels: empty list on input"
  _ -> let
        labels = map (\ (x,
                                 y,
                                 G_sign lid (ExtSign sign symb) ind) -> let
             s_id = mkSimpleId $ "Flattening 3:"++(show x)
             NodeName _ nm _ = dgn_name $ labDG dg (head x)
             n_theory = noSensGTheory lid (ExtSign sign symb) ind
             n_name = NodeName s_id nm 0
             n_info = newNodeInfo DGFlattening
            in
             (y,newInfoNodeLab n_name n_info n_theory)) tripls
       in
        return labels

 createLinks :: DGraph -> (LNode DGNodeLab) -> [Node] -> DGraph
 createLinks dg  _ [] = dg
 createLinks dg (nd,lb) (hd:tl) =
  let
   sign_source = signOf  (dgn_theory lb)
   sign_target = signOf (dgn_theory $ labDG dg hd)
   n_edg = (do
             ng_morphism <- ginclusion logicGraph sign_source sign_target
             return (nd, hd, DGLink { dgl_morphism = ng_morphism,
                                      dgl_type = GlobalDef,
                                      dgl_origin = DGLinkFlatteningThree,
                                      dgl_id = defaultEdgeId }))
   rule = [FlatteningThree]
   change = [InsertEdge(propagateErrors n_edg)]
   (u_dg,u_change) = updateDGAndChanges dg change
   n_dg = addToProofHistoryDG (rule,u_change) u_dg
  in
   createLinks n_dg (nd,lb) tl

 searchForLink :: ([Node],Node,G_sign)
                  -> [([Node],Node,G_sign)]
                  -> [Node]
 searchForLink el@(nds1,_,_) down_level = case down_level of
  [] -> []
  (nds2,nd2,_):tl ->  if containedInList nds2 nds1
                           then nd2:searchForLink el tl
                                 else searchForLink el tl

 linkLevels :: DGraph
               -> [([Node],Node,G_sign)]
               -> [([Node],Node,G_sign)]
               -> DGraph
 linkLevels dg up_level down_level = case up_level of
  [] -> dg
  (hd@(_,nd,_)):tl -> let
            nds = searchForLink hd down_level
            label = labDG dg nd
            n_dg = createLinks dg (nd,label) nds
           in
            linkLevels n_dg tl down_level

 createFirstLevel :: DGraph -> [Node] -> (DGraph,[([Node],Node,G_sign)])
 createFirstLevel dg nds =
  let
   combs = getAllCombinations 2 nds
   init_level = map (\ [x,y] -> let
                                 signx = signOf $ dgn_theory (labDG dg x)
                                 signy = signOf $ dgn_theory (labDG dg y)
                                 n_sign = getIntersectionOfAll [signx
                                                               ,signy]
                                in
                                 ([x,y],propagateErrors n_sign)) combs
   n_empty = filter (\ (_,sign@(G_sign lid _ _)) ->
                               sign /= emptyG_sign (Logic lid)) init_level
  in
   case length n_empty of
    0 -> (dg,[])
    _ -> let
          atch_level = attachNewNodes n_empty (getNewNodeDG dg)
          labels = createLabels dg atch_level
          changes = map (\ x ->
                         InsertNode(x)) (propagateErrors labels)
          rules = replicate (length changes) FlatteningThree
          (u_dg,u_changes) = updateDGAndChanges dg changes
          n_dg = addToProofHistoryDG (rules,u_changes) u_dg
          zero_level = map (\ x ->
                        ([x],x,signOf $ dgn_theory (labDG n_dg x))) nds
          lnk_dg = linkLevels n_dg atch_level zero_level
         in
          (lnk_dg,atch_level)

 createNewLevel :: DGraph
                   -> [Node]
                   -> [([Node],Node,G_sign)]
                   -> (DGraph,[([Node],Node,G_sign)])
 createNewLevel c_dg nds tripls = case tripls of
  [] -> (c_dg,[])
  (_,_,_):[] -> (c_dg,tripls)
  (nd_s, _, _):_ -> case (length nd_s -length nds) of
   0 -> (c_dg,[])
   _ -> let
     combs = getAllCombinations (length nd_s +1) nds
     n_level = catMaybes
                   (map (\ x -> matchCombinations x tripls) combs)
    in
     case length n_level of
      0 -> (c_dg,[])
      _ -> let
            atch_level = attachNewNodes n_level (getNewNodeDG c_dg)
            labels = createLabels c_dg atch_level
            chngs = map (\ x -> InsertNode(x))
                                (propagateErrors labels)
            rls = replicate (length chngs) FlatteningThree
            (u_dg,u_changes) = updateDGAndChanges c_dg chngs
            n_dg = addToProofHistoryDG (rls,u_changes) u_dg
            lnk_dg = linkLevels n_dg atch_level tripls
           in
            (lnk_dg, atch_level)

 -- iterate the procedure for all levels
 -- (the level passed is already inserted in the graph)
 iterateForAllLevels :: DGraph
                        -> [Node]
                        -> [([Node],Node,G_sign)]
                        -> DGraph
 iterateForAllLevels i_dg nds init_level =
  case ((length init_level)<2) of
   False -> let
             (n_dg, n_level) = createNewLevel i_dg nds init_level
            in
             case length n_level of
              0 -> n_dg
              _ -> iterateForAllLevels n_dg nds n_level
   True -> i_dg

 applyToAllNodes :: DGraph -> [Node] -> DGraph
 applyToAllNodes a_dg nds = case nds of
  [] ->  a_dg
  hd:tl -> let
            inc_nds = map (\ (x,_,_) -> x) (innDG a_dg hd)
            (init_dg,init_level) = createFirstLevel a_dg inc_nds
            final_dg = iterateForAllLevels init_dg inc_nds init_level
            o_hist = proofHistory a_dg
            n_hist = proofHistory final_dg
            dif_hist = unzipProofHistory $ take (length n_hist -
                                                 length o_hist)
                                                n_hist
            changes = reverse $ snd (head dif_hist)
            rules = fst (head dif_hist)
           in
            applyToAllNodes final_dg
                            {proofHistory =  [(rules,changes)] ++ o_hist}
                            tl

libEnv_flattening3 :: LibEnv -> Result LibEnv
libEnv_flattening3 lib = do
 new_lib_env <- mapM (\ (l_name,_) -> do
         n_dg <- dg_flattening3 lib l_name
         return $ (l_name, n_dg)) $ Map.toList lib
 return $ Map.fromList new_lib_env
