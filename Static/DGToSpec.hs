{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

Convert development graph back to structured specification
   and compute theory
-}

module Static.DGToSpec
where

import Logic.Logic
import Logic.Grothendieck
import Static.DevGraph
import Syntax.AS_Library
import Syntax.AS_Structured
import Common.AS_Annotation
import Logic.Prover
import Common.Result
import Common.Id
import Common.Utils
import Data.Graph.Inductive.Graph

dgToSpec :: DGraph -> Node -> Result SPEC
dgToSpec dg node = do
  let (_,_,n,preds) = safeContext "Static.DGToSpec.dgToSpec" dg node
  predSps <- sequence (map (dgToSpec dg . snd) preds)
  let apredSps = map emptyAnno predSps
      pos = nullRange
  case n of
    DGNode _ (G_theory lid1 sigma sen') _ _ DGBasic _ _ ->
      do let b = Basic_spec $ G_basic_spec lid1 $
                 sign_to_basic_spec lid1 sigma $ toNamedList sen'
         if null apredSps
          then return b
          else return (Extension (apredSps++[emptyAnno b]) pos)
    DGRef name _ _ _ _ _ -> return (Spec_inst (getName name) [] pos)
    _ -> case dgn_origin n of
        DGExtension ->
         return (Extension apredSps pos)
        DGUnion ->
         return (Union apredSps pos)
        DGTranslation ->
         return (Translation (head apredSps) (Renaming [] nullRange))
        DGHiding ->
         return (Reduction (head apredSps) (Hidden [] nullRange))
        DGRevealing ->
         return (Reduction (head apredSps) (Hidden [] nullRange))
        DGFree ->
         return (Free_spec (head apredSps) pos)
        DGCofree ->
         return (Cofree_spec (head apredSps) pos)
        DGSpecInst name ->
         return (Spec_inst name [] pos)
        _ -> return (Extension apredSps pos)

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
      nodeLab = lab' $ safeContext "Static.DGToSpec.computeLocalTheory"
                dgraph node
      refLn = dgn_libname nodeLab


{- returns all edges that go directly in the given node,
   in case of a DGRef node also all ingoing edges of the referenced node
   are returned -}
-- --------------------------------------
-- methods to determine or get morphisms
-- --------------------------------------

-- determines the morphism of a given path
calculateMorphismOfPath :: [LEdge DGLinkLab] -> Maybe GMorphism
calculateMorphismOfPath [] = Nothing
calculateMorphismOfPath ((_src,_tgt,edgeLab):furtherPath) =
  case maybeMorphismOfFurtherPath of
    Nothing -> if null furtherPath then Just morphism else Nothing
    Just morphismOfFurtherPath ->
      resultToMaybe $ compHomInclusion morphism morphismOfFurtherPath

  where
    morphism = dgl_morphism edgeLab
    maybeMorphismOfFurtherPath = calculateMorphismOfPath furtherPath

-- ------------------------------------
-- methods to get the nodes of an edge
-- ------------------------------------
getSourceNode :: LEdge DGLinkLab -> Node
getSourceNode (source,_,_) = source

getTargetNode :: LEdge DGLinkLab -> Node
getTargetNode (_,target,_) = target

isGlobalDef :: LEdge DGLinkLab -> Bool
isGlobalDef (_,_,edgeLab) =
  case dgl_type edgeLab of
    GlobalDef -> True
    _ -> False

isLocalDef :: LEdge DGLinkLab -> Bool
isLocalDef (_,_,edgeLab) =
  case dgl_type edgeLab of
    LocalDef -> True
    _ -> False

-- | or two predicates
liftOr :: (a -> Bool) -> (a -> Bool) -> a -> Bool
liftOr f g x = f x || g x

-- | Compute the theory of a node (CASL Reference Manual, p. 294, Def. 4.9)
computeTheory :: LibEnv -> LIB_NAME -> Node -> Result G_theory
computeTheory libEnv ln n =
  let dg = lookupDGraph ln libEnv
      nodeLab = lab' $ safeContext "Static.DGToSpec.computeTheory" dg n
      inEdges = filter (liftOr isLocalDef isGlobalDef) $ inn dg n
      localTh = dgn_theory nodeLab
  in if isDGRef nodeLab then let refLn = dgn_libname nodeLab in do
          refTh <- computeTheory libEnv refLn $ dgn_node nodeLab
          flatG_sentences localTh [theoremsToAxioms $ refTh]
     else do
  ths <- mapM (computePathTheory libEnv ln) inEdges
  flatG_sentences localTh ths

computePathTheory :: LibEnv -> LIB_NAME -> LEdge DGLinkLab -> Result G_theory
computePathTheory libEnv ln e@(src, _, link) = do
  th <- if isLocalDef e then computeLocalTheory libEnv ln src
          else computeTheory libEnv ln src
  -- translate theory and turn all imported theorems into axioms
  translateG_theory (dgl_morphism link) $ theoremsToAxioms th

theoremsToAxioms :: G_theory -> G_theory
theoremsToAxioms (G_theory lid sign sens) =
   G_theory lid sign $ markAsAxiom True sens
