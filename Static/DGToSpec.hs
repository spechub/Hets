{- |
Module      :  $Header$
Description :  Conversion of development graph back to structured specification
Copyright   :  (c) Till Mossakowski, C. Maeder, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

Convert development graph back to structured specification
  and compute theory
-}

module Static.DGToSpec
    ( dgToSpec
    ) where

import Logic.Logic
import Logic.Grothendieck
import Static.DevGraph
import Static.GTheory

import Syntax.AS_Structured
import Common.AS_Annotation
import Logic.Prover

import Common.Id
import Common.ExtSign
import Data.Graph.Inductive.Graph


import Control.Monad


-- | convert a node of a development graph back into a specification
dgToSpec :: Monad m => DGraph -> Node -> m SPEC
dgToSpec dg = return . dgToSpec0 dg

dgToSpec0 :: DGraph -> Node -> SPEC
dgToSpec0 dg node = case matchDG node dg of
  (Just (preds, _, n, _), subdg) ->
   let apredSps = map (emptyAnno . dgToSpec0 subdg . snd) preds
       myhead l = case l of
                    [x] -> x
                    _ -> error "dgToSpec0.myhead"
   in if isDGRef n then
          Spec_inst (getName $ dgn_name n) [] nullRange
      else if dgn_origin n == DGBasic then case dgn_theory n of
         G_theory lid1 (ExtSign sigma _) _ sen' _ ->
           let b = Basic_spec (G_basic_spec lid1 $
                 sign_to_basic_spec lid1 sigma $ toNamedList sen') nullRange
           in if null apredSps then b
              else Extension (apredSps ++ [emptyAnno b]) nullRange
      else case dgn_origin n of
        DGExtension ->
         (Extension apredSps nullRange)
        DGUnion ->
         (Union apredSps nullRange)
        DGTranslation ->
         (Translation (myhead apredSps) (Renaming [] nullRange))
        DGHiding ->
         (Reduction (myhead apredSps) (Hidden [] nullRange))
        DGRevealing ->
         (Reduction (myhead apredSps) (Hidden [] nullRange))
        DGFree ->
         (Free_spec (myhead apredSps) nullRange)
        DGCofree ->
         (Cofree_spec (myhead apredSps) nullRange)
        DGSpecInst name ->
         (Spec_inst name [] nullRange)
        _ -> (Extension apredSps nullRange)
  _ -> error "dgToSpec0"

{- compute the theory of a given node.
   If this node is a DGRef, the referenced node is looked up first. -}
computeLocalTheory :: Monad m => LibEnv -> LIB_NAME -> Node -> m G_theory
computeLocalTheory libEnv ln node =
  if isDGRef nodeLab
    then
      computeLocalTheory libEnv refLn $ dgn_node nodeLab
    else return $ dgn_theory nodeLab
    where
      dgraph = lookupDGraph ln libEnv
      nodeLab = labDG dgraph node
      refLn = dgn_libname nodeLab

-- determines the morphism of a given path
calculateMorphismOfPath :: [LEdge DGLinkLab] -> Maybe GMorphism
calculateMorphismOfPath p = case p of
  (_, _, lbl) : r -> let morphism = dgl_morphism lbl in
    if null r then Just morphism else do
       rmor <- calculateMorphismOfPath r
       resultToMaybe $ compInclusion logicGraph morphism rmor
  [] -> error "calculateMorphismOfPath"

isGlobalDef :: DGLinkType -> Bool
isGlobalDef lt = case lt of
    GlobalDef -> True
    _ -> False

isLocalDef :: DGLinkType -> Bool
isLocalDef lt = case lt of
    LocalDef -> True
    _ -> False

liftE :: (DGLinkType -> Bool) -> LEdge DGLinkLab -> Bool
liftE f (_, _, edgeLab) = f $ dgl_type edgeLab

-- | or two predicates
liftOr :: (a -> Bool) -> (a -> Bool) -> a -> Bool
liftOr f g x = f x || g x

-- | Compute the theory of a node (CASL Reference Manual, p. 294, Def. 4.9)
computeTheory :: LibEnv -> LIB_NAME -> Node -> Result G_theory
computeTheory libEnv ln n =
  let dg = lookupDGraph ln libEnv
      nodeLab = labDG dg n
      inEdges = filter (liftE $ liftOr isLocalDef isGlobalDef) $ innDG dg n
      localTh = dgn_theory nodeLab
  in if isDGRef nodeLab then let refLn = dgn_libname nodeLab in do
          refTh <- computeTheory libEnv refLn $ dgn_node nodeLab
          flatG_sentences localTh [theoremsToAxioms $ refTh]
     else do
  ths <- mapM (computePathTheory libEnv ln) $ sortBy
         (\ (_, _, l1) (_, _, l2) -> compare (dgl_id l2) $ dgl_id l1) inEdges
  flatG_sentences localTh ths

computePathTheory :: LibEnv -> LIB_NAME -> LEdge DGLinkLab -> Result G_theory
computePathTheory libEnv ln e@(src, _, link) = do
  th <- if liftE isLocalDef e then computeLocalTheory libEnv ln src
          else computeTheory libEnv ln src
  -- translate theory and turn all imported theorems into axioms
  translateG_theory (dgl_morphism link) $ theoremsToAxioms th

theoremsToAxioms :: G_theory -> G_theory
theoremsToAxioms (G_theory lid sign ind1 sens ind2) =
  G_theory lid sign ind1 (markAsAxiom True sens) ind2
