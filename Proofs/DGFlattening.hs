{- |
Module      :  $Header$
Description :  flattening parts of development graphs
Copyright   :  (c) Igor Stassiy, DFKI Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

In this module we introduce flattening of the graph:

Flattening importings - deleting all inclusion links,
 and inserting a new node, with new computed theory (computeTheory).

Flattening non-disjoint unions - for each node with more than two importings
 modify importings in such a way that at each level, only non-disjoint
 signatures are imported.

Flattening renaming - deterimining renaming link,
inserting a new node with the renaming morphism applied to theory of a
source, deleting the link and setting a new inclusion link between a
new node and the target node.

Flattening hiding links - for each compute normal form if there is such
 and eliminate hiding links.

Flattening heterogeneity - for each heterogeneous link, compute theory of
 a target node and eliminate heterogeneous link.

-}

module Proofs.DGFlattening
  ( dgFlatImports
  , libFlatImports   -- importing
  , dgFlatDUnions
  , libFlatDUnions   -- non-disjoint unions
  , dgFlatRenamings
  , libFlatRenamings -- import with renaming
  , dgFlatHiding
  , libFlatHiding    -- hiding
  , dgFlatHeterogen
  , libFlatHeterogen -- heterogeniety
  , singleTreeFlatDUnions
  ) where

import Common.ExtSign
import Common.Id
import Common.LibName
import Common.Result

import Comorphisms.LogicGraph

import Logic.Coerce
import Logic.Grothendieck
import Logic.Logic

import Static.ComputeTheory
import Proofs.EdgeUtils
import Proofs.NormalForm

import Static.DevGraph
import Static.GTheory
import Static.History

import Data.Graph.Inductive.Graph hiding (empty)
import Data.List
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

mkFlatStr :: String -> DGRule
mkFlatStr = DGRule . ("Flat " ++)

flatImports :: DGRule
flatImports = mkFlatStr "all imports"

flatNonDisjUnion :: DGRule
flatNonDisjUnion = mkFlatStr "non-disjoint union"

flatRename :: DGRule
flatRename = mkFlatStr "renaming"

flatHide :: DGRule
flatHide = mkFlatStr "hiding"

flatHet :: DGRule
flatHet = mkFlatStr "heterogeneity"

-- given a node in a library, gives the node at the end of the reference chain
-- in the library
lookUpReferenceChain :: LibEnv -> LibName -> Node -> (LibName, Node)
lookUpReferenceChain lib_Env libName nd = let
  dg = lookupDGraph libName lib_Env
  in case lookupInRefNodesDG nd dg of
   Just (n_lib, n_nd) -> lookUpReferenceChain lib_Env n_lib n_nd
   Nothing -> (libName, nd)

cErr :: String -> Node -> a
cErr str n = error $ str ++ " no global theory for node " ++ show n

-- this function performs flattening of import links
dgFlatImports :: LibEnv -> LibName -> DGraph -> DGraph
dgFlatImports libEnv ln dg = let
  nds = nodesDG dg
  -- part for dealing with the graph itself
  updLib = updateLib libEnv ln nds
  updDG = lookupDGraph ln updLib
  -- it seems changes of the labels are lost and all edges are simply deleted
  n_dg = changesDGH dg $ map DeleteEdge $ labEdgesDG updDG
  in groupHistory dg flatImports n_dg
  where
   updateNode :: LibEnv -> LibName -> Node -> DGChange
   updateNode lib_Env l_n n =
    let
     labRf = labDG (lookupDGraph l_n lib_Env) n
      -- have to consider references here. computeTheory is applied
      -- to the node at the end of the chain of references only.
    in case computeTheory lib_Env l_n n of
         Just ndgn_theory ->
           SetNodeLab labRf (n, labRf {dgn_theory = ndgn_theory})
         Nothing ->
           cErr "dgFlatImports" n
   updateLib :: LibEnv -> LibName -> [Node] -> LibEnv
   updateLib lib_Env l_n nds =
    case nds of
     [] -> lib_Env
     hd : tl -> let
               change = updateNode lib_Env l_n hd
               ref_dg = lookupDGraph l_n lib_Env
               u_dg = changeDGH ref_dg change
               new_dg = groupHistory ref_dg flatImports u_dg
              in
               updateLib (Map.insert l_n new_dg lib_Env) l_n tl

-- this function performs flattening of imports for the whole library
libFlatImports :: LibEnv -> Result LibEnv
libFlatImports lib = return $ Map.mapWithKey (dgFlatImports lib) lib

-- this function performs flattening of imports with renamings
-- links for a given developement graph
dgFlatRenamings :: LibEnv -> LibName -> DGraph -> DGraph
dgFlatRenamings lib_Env l_n dg =
  let
   l_edges = labEdgesDG dg
   renamings = filter (\ (_, _, x) -> let l_type = getRealDGLinkType x in
     case l_type of
       DGEdgeType { edgeTypeModInc = GlobalDef, isInc = False} -> True
       _ -> False ) l_edges
   fin_dg = applyUpdDG renamings dg
  -- no need to care about references as each node
  -- is preserved during flattening.
  in computeDGraphTheories lib_Env fin_dg
    where
     updateDGWithChanges :: LEdge DGLinkLab -> DGraph -> DGraph
     updateDGWithChanges l_edg@( v1, v2, label) d_graph =
      let
      -- update nodes
       lv1 = labDG d_graph v1
       lv2 = labDG d_graph v2
       name = dgn_name lv1
       n_node = getNewNodeDG d_graph
       nlv1 = case computeTheory lib_Env l_n v1 of
         Just n_dgn_theory -> lv1 {dgn_theory = n_dgn_theory }
         Nothing -> cErr "dgFlatRenamings1" v1
       nlv2 = case computeTheory lib_Env l_n v2 of
         Just n_dgn_theory -> lv2 {dgn_theory = n_dgn_theory }
         Nothing -> cErr "dgFlatRenamings2" v2
       n_lnode@(_, n_lv) = propagateErrors "dgFlatRenamings3" $ do
             t_dgn_theory <- translateG_theory (dgl_morphism label)
                             $ dgn_theory nlv1
             return (n_node, newInfoNodeLab name
                                     (newNodeInfo DGFlattening)
                                     t_dgn_theory)
       -- create edge
       sign_source = signOf $ dgn_theory n_lv
       sign_target = signOf $ dgn_theory lv2
       n_edg = do
                 ng_morphism <- ginclusion logicGraph sign_source sign_target
                 return (n_node,
                         v2,
                         label { dgl_morphism = ng_morphism,
                                 dgl_type = globalDef ,
                                 dgl_origin = DGLinkFlatteningRename,
                                 dgl_id = defaultEdgeId })
       change_dg = [SetNodeLab lv1 (v1, nlv1),
                    SetNodeLab lv2 (v2, nlv2),
                    DeleteEdge l_edg,
                    InsertNode n_lnode,
                    InsertEdge (propagateErrors "dgFlatRenamings4" n_edg)]
      in
       changesDGH d_graph change_dg

     applyUpdDG :: [LEdge DGLinkLab] -> DGraph -> DGraph
     applyUpdDG l_list d_g = case l_list of
      [] -> d_g
      hd : tl -> let
                dev_g = updateDGWithChanges hd d_g
               in applyUpdDG tl $ groupHistory d_g flatRename dev_g

-- this function performs flattening of imports with renamings
libFlatRenamings :: LibEnv -> Result LibEnv
libFlatRenamings lib = return $ Map.mapWithKey (dgFlatRenamings lib) lib

-- this function performs flattening of hiding links
dgFlatHiding :: DGraph -> DGraph
dgFlatHiding dg = let
   hids = filter (\ (_, _, x) -> (case dgl_type x of
                                         HidingDefLink -> True
                                         _ -> False)) $ labEdgesDG dg
  -- no need to care about references either, as nodes are preserved
  -- after flattening, as well as references.
   n_dg = changesDGH dg $ map DeleteEdge hids
  in groupHistory dg flatHide n_dg

-- this function performs flattening of heterogeniety for the whole library
libFlatHiding :: LibEnv -> Result LibEnv
libFlatHiding = fmap (Map.map dgFlatHiding) . normalFormLibEnv

-- this function performs flattening of heterogeniety
-- for a given developement graph
dgFlatHeterogen :: LibEnv -> LibName -> DGraph -> DGraph
dgFlatHeterogen libEnv ln dg = let
  het_comorph = filter
    (\ (_, _, x) -> not $ isHomogeneous $ dgl_morphism x) $ labEdgesDG dg
  het_del_changes = map DeleteEdge het_comorph
  updLib = updateNodes libEnv ln . Set.toList . Set.fromList
    $ map ( \ (_, t, l) -> (t, isDefEdge $ dgl_type l)) het_comorph
  udg = lookupDGraph ln updLib
  ndg = changesDGH udg het_del_changes
  in groupHistory udg flatHet ndg
  where
   updateNodes :: LibEnv -> LibName -> [(Node, Bool)] -> LibEnv
   updateNodes lib_Env l_n nds = case nds of
    [] -> lib_Env
    (hd, isHetDef) : tl -> let
      -- have to consider references here. computeTheory is applied to the
      -- node at the end of the chain of references only.
      (lname, nd) = lookUpReferenceChain lib_Env l_n hd
      odg = lookupDGraph lname lib_Env
      labRf = labDG odg nd
      change = case computeTheory lib_Env lname nd of
        Just ndgn_theory ->
          SetNodeLab labRf (nd, labRf {dgn_theory = ndgn_theory})
        Nothing -> cErr "dgFlatHeterogen" nd
      cdg = changeDGH odg change
      n_dg = groupHistory odg flatHet cdg
     in updateNodes (if isHetDef then Map.insert lname n_dg lib_Env
                    else lib_Env) l_n tl

-- this function performs flattening of heterogeniety for the whole library
libFlatHeterogen :: LibEnv -> Result LibEnv
libFlatHeterogen lib =
  return $ Map.mapWithKey (dgFlatHeterogen lib) lib

-- this function performs flattening of non-disjoint unions for the given
-- DGraph
dgFlatDUnions :: LibEnv -> DGraph -> DGraph
dgFlatDUnions le dg =
 let
  all_nodes = nodesDG dg
  imp_nds = filter (\ x -> length (innDG dg x) > 1) all_nodes
 -- lower_nodes = filter (\ x -> (outDG dg x == [])) (nodesDG dg)
 -- as previously, no need to care about reference nodes,
 -- as previous one remain same.
 in computeDGraphTheories le $ applyToAllNodes dg imp_nds

-- this funciton given a list og G_sign returns intersection of them
getIntersectionOfAll :: [G_sign] -> G_sign
getIntersectionOfAll signs =
  case signs of
   [] -> error "getIntersectionOfAll1: empty signatures list"
   [hd] -> hd
   G_sign lid1 extSign1 _ : G_sign lid2 (ExtSign signtr2 _) _ : tl -> let
            n_signtr = propagateErrors "getIntersectionOfAll2" $ do
               ExtSign sign1 _ <- coerceSign lid1
                                               lid2
                                               "getIntersectionOfAll"
                                               extSign1
               n_sign <- intersection lid2 sign1 signtr2
               return $ G_sign lid2 (mkExtSign n_sign) startSigId
           in
            if n_signtr == emptyG_sign (Logic lid2) then n_signtr
            else getIntersectionOfAll (n_signtr : tl)

-- this function given a list of all possible combinations of nodes
-- of a given length
getAllCombinations :: Int -> [Node] -> [[Node]]
getAllCombinations 0 _ = [ [] ]
getAllCombinations n xs = [ y : ys | y : xs' <- tails xs
                           , ys <- getAllCombinations (n - 1) xs']

-- tells if two lists are equal or one contained in the other
containedInList :: [Node] -> [Node] -> Bool
containedInList l1 l2 = all (`elem` l2) l1

-- attach new nodes to the level
attachNewNodes :: [([Node], G_sign)] -> Int -> [([Node], Node, G_sign)]
attachNewNodes [] _ = []
attachNewNodes ((hd, sg) : tl) n = (hd, n, sg) : attachNewNodes tl (n + 1)

 -- search for a match for a given combination in a level
searchForMatch :: [Node] -> [([Node], Node, G_sign)]
               -> Maybe ([Node], Node, G_sign)
searchForMatch _ [] = Nothing
searchForMatch l (tripl@(nds, _, _) : tl) =
  if containedInList l nds then Just tripl else searchForMatch l tl

 -- take a combination of nodes, previous level,
 -- and get the signature for the next level
matchCombinations :: [Node] -> [([Node], Node, G_sign)]
                  -> Maybe ([Node], G_sign)
matchCombinations [] _ = Nothing
matchCombinations ([_]) _ = Nothing
matchCombinations l@(hd1 : hd2 : tl) trpls =
  case searchForMatch (hd1 : tl) trpls of
   Nothing -> Nothing
   Just (_, _, gsig1@(G_sign lid _ _)) ->
     case searchForMatch (hd2 : tl) trpls of
         Nothing -> Nothing
         Just (_, _, gsig2) ->
            let
             n_sig = getIntersectionOfAll [gsig1, gsig2]
            in
             if n_sig == emptyG_sign (Logic lid) then Nothing
             else Just (l, n_sig)

 -- for a dg and a level, create labels for the new nodes
createLabels :: DGraph -> [([Node], Node, G_sign)] -> [LNode DGNodeLab]
createLabels dg tripls = case tripls of
  [] -> error "createLabels: empty list on input"
  _ -> let
        labels = map (\ (x, y, G_sign lid (ExtSign sign symb) ind) -> let
             -- name intersection by interspersing a string for a SimpleId
             s_id = mkSimpleId . intercalate "'"
               $ map (`getNameOfNode` dg) x
             n_theory = noSensGTheory lid (ExtSign sign symb) ind
             n_name = makeName s_id
             n_info = newNodeInfo DGFlattening
            in
             (y, newInfoNodeLab n_name n_info n_theory)) tripls
       in labels

-- create links connecting given node with a list of nodes
createLinks :: DGraph -> LNode DGNodeLab -> [Node] -> DGraph
createLinks dg _ [] = dg
createLinks dg (nd, lb) (hd : tl) =
  let
   sign_source = signOf (dgn_theory lb)
   sign_target = signOf (dgn_theory $ labDG dg hd)
   n_edg = propagateErrors "DGFlattening.createLinks" $ do
      ng_morphism <- ginclusion logicGraph sign_source sign_target
      return (nd, hd, globDefLink ng_morphism DGLinkFlatteningUnion)
   u_dg = case tryToGetEdge n_edg dg of
            Nothing -> changeDGH dg $ InsertEdge n_edg
            Just _ -> dg
   n_dg = groupHistory dg flatNonDisjUnion u_dg
  in
   createLinks n_dg (nd, lb) tl

-- given an element in the level and a lower link, function searches
-- elements in the given level, which are suitable for inserting a link
-- connecting given element.
searchForLink :: ([Node], Node, G_sign) -> [([Node], Node, G_sign)] -> [Node]
searchForLink el@(nds1, _, _) down_level = case down_level of
  [] -> []
  (nds2, nd2, _) : tl -> [ nd2 | containedInList nds2 nds1 ]
                         ++ searchForLink el tl

-- given two levels of the graph, insert links between them, so that the
-- signatures are imported properly
linkLevels :: DGraph -> [([Node], Node, G_sign)] -> [([Node], Node, G_sign)]
           -> DGraph
linkLevels dg up_level down_level = case up_level of
  [] -> dg
  hd@(_, nd, _) : tl -> let
            nds = searchForLink hd down_level
            label = labDG dg nd
            n_dg = createLinks dg (nd, label) nds
           in
            linkLevels n_dg tl down_level

-- given a list of the lower nodes, gives a DGraph with a first level
-- of nodes inserted in this graph
createFirstLevel :: DGraph -> [Node] -> (DGraph, [([Node], Node, G_sign)])
createFirstLevel dg nds =
  let
   combs = getAllCombinations 2 nds
   init_level = map (\ l -> let  [x, y] = l
                                 signx = signOf $ dgn_theory (labDG dg x)
                                 signy = signOf $ dgn_theory (labDG dg y)
                                 n_sign = getIntersectionOfAll [signx
                                                               , signy]
                                in
                                 (l, n_sign)) combs
   n_empty = filter (\ (_, sign@(G_sign lid _ _)) ->
                               sign /= emptyG_sign (Logic lid)) init_level
  in
   case length n_empty of
    0 -> (dg, [])
    _ -> let
          atch_level = attachNewNodes n_empty (getNewNodeDG dg)
          labels = createLabels dg atch_level
          changes = map InsertNode labels
          u_dg = changesDGH dg changes
          n_dg = groupHistory dg flatNonDisjUnion u_dg
          zero_level = map (\ x ->
                        ([x], x, signOf $ dgn_theory (labDG n_dg x))) nds
          lnk_dg = linkLevels n_dg atch_level zero_level
         in
          (lnk_dg, atch_level)

-- given a level of nodes and a graph, constructs upper level,
-- inserting the nodes of the new level to the DGraph
createNewLevel :: DGraph -> [Node] -> [([Node], Node, G_sign)]
               -> (DGraph, [([Node], Node, G_sign)])
createNewLevel c_dg nds tripls = case tripls of
  [] -> (c_dg, [])
  [_] -> (c_dg, tripls)
  (nd_s, _, _) : _ -> if length nd_s - length nds == 0 then (c_dg, [])
    else let
     combs = getAllCombinations (length nd_s + 1) nds
     n_level = mapMaybe (`matchCombinations` tripls) combs
    in if null n_level then (c_dg, []) else
           let
            atch_level = attachNewNodes n_level (getNewNodeDG c_dg)
            labels = createLabels c_dg atch_level
            chngs = map InsertNode labels
            u_dg = changesDGH c_dg chngs
            n_dg = groupHistory c_dg flatNonDisjUnion u_dg
            lnk_dg = linkLevels n_dg atch_level tripls
           in
            (lnk_dg, atch_level)

 -- iterate the procedure for all levels
 -- (the level passed is already inserted in the graph)
iterateForAllLevels :: DGraph -> [Node] -> [([Node], Node, G_sign)] -> DGraph
iterateForAllLevels i_dg nds init_level =
  if length init_level < 2 then i_dg else
   let (n_dg, n_level) = createNewLevel i_dg nds init_level
   in if null n_level then n_dg else
         iterateForAllLevels n_dg nds n_level

-- applies itteration for all the nodes in the graph
applyToAllNodes :: DGraph -> [Node] -> DGraph
applyToAllNodes a_dg nds = case nds of
 [] -> a_dg
 hd : tl -> let
            inc_nds = map (\ (x, _, _) -> x) (innDG a_dg hd)
            (init_dg, init_level) = createFirstLevel a_dg inc_nds
            final_dg = iterateForAllLevels init_dg inc_nds init_level
           in
            applyToAllNodes final_dg tl
-- given a lower level of nodes, gives upper level of nodes,
-- which are ingoing nodes for the lower level
filterIngoing :: DGraph -> [Node] -> [Node]
filterIngoing dg nds = case nds of
  [] -> []
  hd : tl -> let ind = map (\ (x, _, _) -> x) (innDG dg hd) in
             ind ++ filterIngoing dg (ind ++ tl)

-- this function takes a node and performs flattening
-- of non-disjoint unions for the ingoing tree of nodes to the given node
singleTreeFlatDUnions :: LibEnv -> LibName -> Node -> Result LibEnv
singleTreeFlatDUnions libEnv libName nd = let
  dg = lookupDGraph libName libEnv
  in_nds = filterIngoing dg [nd]
  n_dg = applyToAllNodes dg in_nds
  in return $ Map.insert libName n_dg libEnv

-- this functions performs flattening of
-- non-disjoint unions for the whole library
libFlatDUnions :: LibEnv -> Result LibEnv
libFlatDUnions le = return $ Map.map (dgFlatDUnions le) le
