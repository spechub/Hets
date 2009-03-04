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

Flattening non-disjoint unions - for each node with more than two importings
 modify importings in such a way that at each level, only non-disjoint signatures
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

module Proofs.DGFlattening (dg_flattening_imports,
                            libEnv_flattening_imports,   -- importing
                            dg_flattening_dunions,
                            libEnv_flattening_dunions,   -- non-disjoint unions
                            dg_flattening_renamings,
                            libEnv_flattening_renamings, -- import with renaming
                            dg_flattening_hiding,
                            libEnv_flattening_hiding,    -- hiding
                            dg_flattening_heterogen,
                            libEnv_flattening_heterogen, -- heterogeniety
                            singleTree_flattening_dunions
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
import Proofs.NormalForm
import Common.Result
import Common.ExtSign
import Common.LibName
import Data.Graph.Inductive.Graph hiding (empty)
import Data.List (tails)
import Data.Maybe(fromJust,isJust)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad
import Common.Id

-- change the strings to make them more expressive
flat1 :: DGRule
flat1 = DGRule "FlatteningOne"

flat3 :: DGRule
flat3 = DGRule "FlatteningThree"

flat4 :: DGRule
flat4 = DGRule "FlatteningFour"

flat5 :: DGRule
flat5 = DGRule "FlatteningFive"

flat6 :: DGRule
flat6 = DGRule "FlatteningSix"


-- given a node in a library, gives the node at the end of the reference chain
-- in the library
lookUpReferenceChain :: LibEnv -> LIB_NAME -> Node -> (LIB_NAME,Node)
lookUpReferenceChain lib_Env libName nd = let
  dg = (lookupDGraph libName lib_Env)
 in
  case (lookupInRefNodesDG nd dg) of
   Just (n_lib,n_nd) -> lookUpReferenceChain lib_Env n_lib n_nd
   Nothing -> (libName,nd)

-- this function performs flattening of import links for a given developement graph
dg_flattening_imports :: LibEnv -> LIB_NAME -> Result DGraph
dg_flattening_imports libEnv ln = do
 let
  dg = lookupDGraph ln libEnv
  nds = nodesDG dg
  -- part for dealing with the graph itself
  updLib = updateLib libEnv ln nds
  updDG = lookupDGraph ln updLib
  n_dg = changesDGH dg $ map DeleteEdge $ labEdgesDG updDG
 return $ groupHistory dg flat1 n_dg
  where
   updateNode :: LibEnv
                 -> LIB_NAME
                 -> Node
                 -> Result (LibEnv, DGChange)
   updateNode lib_Env l_n n =
    let
     --(lib,nd) = lookUpReferenceChain lib_Env l_n n
     dg = lookupDGraph l_n lib_Env
     labRf = labDG dg n
      -- have to consider references here. computeTheory is applied
      -- to the node at the end of the chain of references only.
    in
     do
      (libEnv2, ndgn_theory) <- computeTheory False lib_Env l_n n
      return $(libEnv2,
               SetNodeLab labRf (n,
               labRf {dgn_theory = ndgn_theory}))

   updateLib :: LibEnv -> LIB_NAME -> [Node] -> LibEnv
   updateLib lib_Env l_n nds =
    case nds of
     [] ->  lib_Env
     hd : tl -> let
               (libEnv2, change) = propagateErrors (updateNode lib_Env
                                                              l_n
                                                              hd)
               ref_dg = lookupDGraph l_n libEnv2
               u_dg = changeDGH ref_dg change
               new_dg = groupHistory ref_dg flat1 u_dg
              in
               updateLib (Map.insert l_n new_dg libEnv2) l_n tl

-- this function performs flattening of imports for the whole library
libEnv_flattening_imports :: LibEnv -> Result LibEnv
libEnv_flattening_imports lib = do
        new_lib_env <- mapM (\ (x,_) -> do
                         z <- dg_flattening_imports lib x
                         return (x, z)) $ Map.toList lib
        return $ Map.fromList new_lib_env

-- this function performs flattening of imports with renamings
-- links for a given developement graph
dg_flattening_renamings :: LibEnv -> LIB_NAME -> DGraph
dg_flattening_renamings lib_Env l_n =
  let
   dg = lookupDGraph l_n lib_Env
   l_edges = labEdgesDG dg
   renamings = Prelude.filter (\ (_,_,x) -> let l_type = getRealDGLinkType x in
     case l_type of
       DGEdgeType { edgeTypeModInc = HomGlobalDef, isInc = False} -> True
       _ -> False ) l_edges
   fin_dg = applyUpdDG renamings dg
  -- no need to care about references as each node
  -- is preserved during flattening.
  in fin_dg
    where
     updateDGWithChanges :: LEdge DGLinkLab -> DGraph -> DGraph
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
                    DeleteEdge l_edg,
                    InsertNode (propagateErrors n_lnode),
                    InsertEdge (propagateErrors n_edg)]
      in
       changesDGH d_graph change_dg

     applyUpdDG :: [LEdge DGLinkLab] -> DGraph -> DGraph
     applyUpdDG l_list d_g = case l_list of
      [] -> d_g
      hd : tl -> let
                dev_g = updateDGWithChanges hd d_g
               in applyUpdDG tl $ groupHistory d_g flat4 dev_g

-- this function performs flattening of imports with renamings for a given developement graph
libEnv_flattening_renamings :: LibEnv -> Result LibEnv
libEnv_flattening_renamings libEnv =
       let
        new_lib_env = Prelude.map (\ (x,_) ->
                        let
                         z = dg_flattening_renamings libEnv x
                        in
                         (x, z)) $ Map.toList libEnv
       in
        return $ Map.fromList new_lib_env

-- this function performs flattening of hiding links for a given developement graph
dg_flattening_hiding :: DGraph -> DGraph
dg_flattening_hiding dg = let
   hids = Prelude.filter (\ (_,_,x) -> (case dgl_type x of
                                         HidingDef -> True
                                         _ -> False)) $ labEdgesDG dg
  -- no need to care about references either, as nodes are preserved
  -- after flattening, as well as references.
   n_dg = changesDGH dg $ map DeleteEdge hids
  in groupHistory dg flat5 n_dg

-- this function performs flattening of heterogeniety for the whole library
libEnv_flattening_hiding :: LibEnv -> Result LibEnv
libEnv_flattening_hiding =
  fmap (Map.map dg_flattening_hiding) . normalFormLibEnv

-- this function performs flattening of heterogeniety
-- for a given developement graph
dg_flattening_heterogen :: LibEnv -> LIB_NAME -> Result DGraph
dg_flattening_heterogen libEnv ln = do
 let
  dg = lookupDGraph ln libEnv
  l_edges = labEdgesDG dg
  het_comorph = Prelude.filter (\ (_,_,x) ->
                 let
                  comorph = dgl_morphism x
                 in
                  not $ isHomogeneous comorph) l_edges
  het_del_changes = Prelude.map DeleteEdge het_comorph
  updLib = updateNodes libEnv ln . Set.toList . Set.fromList
    $ map ( \(_, t, _) -> t) het_comorph
  udg = lookupDGraph ln updLib
  ndg = changesDGH udg het_del_changes
 return $ groupHistory udg flat6 ndg
  where
   updateNodes :: LibEnv
                  -> LIB_NAME
                  -> [Node]
                  -> LibEnv
   updateNodes lib_Env l_n nds = case nds of
    [] -> lib_Env
    hd : tl -> let
      -- have to consider references here. computeTheory is applied to the
      -- node at the end of the chain of references only.
      (lname,nd) = lookUpReferenceChain lib_Env l_n hd
      labRf = labDG (lookupDGraph lname lib_Env) nd
      (libEnv2, change) = propagateErrors $ do
        (le, ndgn_theory) <- computeTheory False lib_Env lname nd
        return (le, SetNodeLab labRf (nd, labRf {dgn_theory = ndgn_theory}))
      odg = lookupDGraph lname libEnv2
      cdg = changeDGH odg change
      n_dg = groupHistory odg flat6 cdg
     in
      (updateNodes (Map.insert lname n_dg libEnv2) l_n tl)

-- this function performs flattening of heterogeniety for the whole library
libEnv_flattening_heterogen :: LibEnv -> Result LibEnv
libEnv_flattening_heterogen lib = do
 new_lib_env <- mapM (\ (x,_) -> do
         z <- dg_flattening_heterogen lib x
         return (x, z)) $ Map.toList lib
 return $ Map.fromList new_lib_env

-- this function performs flattening of non-disjoint unions for the given
-- DGraph
dg_flattening_dunions :: LibEnv -> LIB_NAME -> Result DGraph
dg_flattening_dunions libEnv ln = do
 let
  dg = lookupDGraph ln libEnv
  all_nodes = nodesDG dg
  imp_nds = Prelude.filter (\ x -> ( length (innDG dg x) > 1)) all_nodes
 --lower_nodes = Prelude.filter (\ x -> (outDG dg x == [])) (nodesDG dg)
 -- as previously, no need to care about reference nodes,
 -- as previous one remain same.
 return $ applyToAllNodes dg imp_nds

-- this funciton given a list og G_sign returns intersection of them
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

-- this function given a list of all possible combinations of nodes
-- of a given length
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
        labels = Prelude.map (\ (x,
                                 y,
                                 G_sign lid (ExtSign sign symb) ind) -> let
             n_map = (\ z -> let
                              NodeName sid _ _ = dgn_name $ labDG dg z
                             in
                              sid)
             names = show $ Prelude.map n_map  x
             s_id = mkSimpleId $ "Flattening 3:"++(names)
             n_theory = noSensGTheory lid (ExtSign sign symb) ind
             n_name = makeName s_id
             n_info = newNodeInfo DGFlattening
            in
             (y,newInfoNodeLab n_name n_info n_theory)) tripls
       in
        return labels

-- create links connecting given node with a list of nodes
createLinks :: DGraph -> (LNode DGNodeLab) -> [Node] -> DGraph
createLinks dg  _ [] = dg
createLinks dg (nd, lb) (hd:tl) =
  let
   sign_source = signOf  (dgn_theory lb)
   sign_target = signOf (dgn_theory $ labDG dg hd)
   n_edg = propagateErrors $ do
      ng_morphism <- ginclusion logicGraph sign_source sign_target
      return (nd, hd, DGLink { dgl_morphism = ng_morphism,
                               dgl_type = GlobalDef,
                               dgl_origin = DGLinkFlatteningThree,
                               dgl_id = defaultEdgeId })
   u_dg = case tryToGetEdge n_edg dg of
            Nothing -> changeDGH dg $ InsertEdge n_edg
            Just _ -> dg
   n_dg = groupHistory dg flat3 u_dg
  in
   createLinks n_dg (nd, lb) tl

-- given an element in the level and a lower link, function searches
-- elements in the given level, which are suitable for inserting a link
-- connecting given element.
searchForLink :: ([Node],Node,G_sign)
                 -> [([Node],Node,G_sign)]
                 -> [Node]
searchForLink el@(nds1,_,_) down_level = case down_level of
  [] -> []
  (nds2,nd2,_):tl ->  if containedInList nds2 nds1
                           then nd2:searchForLink el tl
                                 else searchForLink el tl

-- given two levels of the graph, insert links between them, so that the
-- signatures are imported properly
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

-- given a list of the lower nodes, gives a DGraph with a first level
-- of nodes inserted in this graph
createFirstLevel :: DGraph -> [Node] -> (DGraph,[([Node],Node,G_sign)])
createFirstLevel dg nds =
  let
   combs = getAllCombinations 2 nds
   init_level = Prelude.map (\ [x,y] -> let
                                 signx = signOf $ dgn_theory (labDG dg x)
                                 signy = signOf $ dgn_theory (labDG dg y)
                                 n_sign = getIntersectionOfAll [signx
                                                               ,signy]
                                in
                                 ([x,y],propagateErrors n_sign)) combs
   n_empty = Prelude.filter (\ (_,sign@(G_sign lid _ _)) ->
                               sign /= emptyG_sign (Logic lid)) init_level
  in
   case length n_empty of
    0 -> (dg,[])
    _ -> let
          atch_level = attachNewNodes n_empty (getNewNodeDG dg)
          labels = createLabels dg atch_level
          changes = Prelude.map InsertNode (propagateErrors labels)
          u_dg = changesDGH dg changes
          n_dg = groupHistory dg flat3 u_dg
          zero_level = Prelude.map (\ x ->
                        ([x],x,signOf $ dgn_theory (labDG n_dg x))) nds
          lnk_dg = linkLevels n_dg atch_level zero_level
         in
          (lnk_dg,atch_level)

-- given a level of nodes and a graph, constructs upper level,
-- inserting the nodes of the new level to the DGraph
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
     n_level = Prelude.map (\ x -> fromJust x) $
                 Prelude.filter (\ x -> isJust x)
                   (Prelude.map (\ x -> matchCombinations x tripls) combs)
    in
     case length n_level of
      0 -> (c_dg,[])
      _ -> let
            atch_level = attachNewNodes n_level (getNewNodeDG c_dg)
            labels = createLabels c_dg atch_level
            chngs = Prelude.map (\ x -> InsertNode(x))
                                (propagateErrors labels)
            u_dg = changesDGH c_dg chngs
            n_dg = groupHistory c_dg flat3 u_dg
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

-- applies itteration for all the nodes in the graph
applyToAllNodes :: DGraph -> [Node] -> DGraph
applyToAllNodes a_dg nds = case nds of
 [] ->  a_dg
 hd:tl -> let
            inc_nds = Prelude.map (\ (x,_,_) -> x) (innDG a_dg hd)
            (init_dg,init_level) = createFirstLevel a_dg inc_nds
            final_dg = iterateForAllLevels init_dg inc_nds init_level
           in
            applyToAllNodes final_dg tl
-- given a lower level of nodes, gives upper level of nodes,
-- which are ingoing nodes for the lower level
filterIngoing :: DGraph -> [Node] -> [Node]
filterIngoing dg nds = case nds of
 [] -> []
 hd:tl -> let
           ind = Prelude.map (\(x,_,_) -> x) (innDG dg hd)
          in
           ind ++ filterIngoing dg (ind ++ tl)

-- this function takes a node and performs flattening
-- of non-disjoint unions for the ingoing tree of nodes to the given node
singleTree_flattening_dunions :: LibEnv
                                 -> LIB_NAME
                                 -> Node
                                 -> Result LibEnv
singleTree_flattening_dunions libEnv libName nd =
 let
  dg = lookupDGraph libName libEnv
  in_nds = filterIngoing dg [nd]
  n_dg = applyToAllNodes dg in_nds
 in
  return $ Map.insert libName n_dg libEnv

-- this functions performs flattening of
-- non-disjoint unions for the whole library
libEnv_flattening_dunions :: LibEnv -> Result LibEnv
libEnv_flattening_dunions lib = do
 new_lib_env <- mapM (\ (l_name,_) -> do
         n_dg <- dg_flattening_dunions lib l_name
         return $ (l_name, n_dg)) $ Map.toList lib
 return $ Map.fromList new_lib_env
