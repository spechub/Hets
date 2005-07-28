{-| 
   
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
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
import Common.Result
import Common.Id
import Data.Graph.Inductive.Graph
import qualified Common.Lib.Map as Map

emptyAnno :: SPEC -> Annoted SPEC
emptyAnno x = Annoted x nullRange [] []

dgToSpec :: DGraph -> Node -> Result SPEC
dgToSpec dg node = do
  let (_,_,n,preds) = context dg node
  predSps <- sequence (map (dgToSpec dg . snd) preds)
  let apredSps = map emptyAnno predSps
      pos = nullRange
  case n of
    (DGNode _ (G_sign lid1 sigma) (G_l_sentence_list lid2 sen) _ _ DGBasic) -> 
      do sen' <- rcoerce lid1 lid2 nullRange sen
         let b = Basic_spec (G_basic_spec lid1 (sign_to_basic_spec lid1 sigma sen'))
         if null apredSps
          then return b
          else return (Extension (apredSps++[emptyAnno b]) pos)
    (DGNode _ _ _ _ _ DGExtension) ->
         return (Extension apredSps pos)
    (DGNode _ _ _ _ _ DGUnion) ->
         return (Union apredSps pos)
    (DGNode _ _ _ _ _ DGTranslation) ->
         return (Translation (head apredSps) (Renaming [] nullRange))
    (DGNode _ _ _ _ _ DGHiding) ->
         return (Reduction (head apredSps) (Hidden [] nullRange))
    (DGNode _ _ _ _ _ DGRevealing) ->
         return (Reduction (head apredSps) (Hidden [] nullRange))
    (DGNode _ _ _ _ _ DGFree) ->
         return (Free_spec (head apredSps) pos)
    (DGNode _ _ _ _ _ DGCofree) ->
         return (Cofree_spec (head apredSps) pos)
    (DGNode _ _ _ _ _ (DGSpecInst name)) ->
         return (Spec_inst name [] pos)
    (DGRef name _ _ _ _) -> return (Spec_inst (getName name) [] pos)
    _ -> return (Extension apredSps pos)

{- compute the theory of a given node. 
   If this node is a DGRef, the referenced node is looked up first. -}
computeLocalTheory :: LibEnv -> LibNode -> Maybe G_theory
computeLocalTheory libEnv (ln,node) =
  if isDGRef nodeLab
    then case Map.lookup refLn libEnv of
      Just _ -> computeLocalTheory libEnv (refLn,dgn_node nodeLab)
      Nothing -> Nothing
    else toG_theory (dgn_sign nodeLab) (dgn_sens nodeLab)
    where
      dgraph = lookupDGraphInLibEnv ln libEnv
      nodeLab = lab' $ context dgraph node
      refLn = dgn_libname nodeLab

{- if the given node is a DGRef, the referenced node is returned (as a
labeled node). Otherwise the node itself is returned (as a labeled
node).-}
getDGNode :: LibEnv -> DGraph -> Node -> Maybe (LNode DGNodeLab)
getDGNode libEnv dgraph node =
  if isDGRef nodeLab then case Map.lookup (dgn_libname nodeLab) libEnv of
      Just (_,_,refDgraph) -> 
         getDGNode libEnv refDgraph (dgn_node nodeLab)
      Nothing -> Nothing
    else Just (labNode' contextOfNode)
  where contextOfNode = context dgraph node
        nodeLab = lab' contextOfNode

type LibNode = (LIB_NAME,Node)
type LibLEdge = (LIB_NAME,LEdge DGLinkLab)

getAllGlobDefPathsBeginningWithTypesTo_new 
    :: (LEdge DGLinkLab -> Bool) -> LibEnv -> LibNode -> [LibLEdge]
    -> [(LibNode, [LibLEdge])]
getAllGlobDefPathsBeginningWithTypesTo_new types libEnv libnode path =
  (libnode,path):(typeGlobPaths ++
    (concat ( [getAllGlobDefPathsBeginningWithTypesTo_new
                   types libEnv nextLibnode newPath |
                       (nextLibnode, newPath) <- globalPaths])
    )
   )

  where
    inEdges = getAllIngoingEdges libEnv libnode
    globalEdges = [libedge| libedge <- filter (isGlobalDef.snd) inEdges,
		   notElem libedge path]
    edgesOfTypes 
        = [libedge| libedge <- filterByTypes_new types inEdges,
	   notElem libedge path]
    globalPaths = [(getSourceLibNode libedge, (libedge:path))|
		   libedge <- globalEdges]
    typeGlobPaths = [(getSourceLibNode libedge, (libedge:path))|
		     libedge <- edgesOfTypes]


getSourceLibNode :: LibLEdge -> LibNode
getSourceLibNode (ln,edge) = (ln, getSourceNode edge)

lookupDGraphInLibEnv :: LIB_NAME -> LibEnv -> DGraph
lookupDGraphInLibEnv ln libEnv =
    case Map.lookup ln libEnv of
    Nothing -> error ("lookupDGraphInLibEnv: Could not find development graph "
		      ++ "with library name " ++(show ln)++ " in given libEnv")
    Just (_,_,dgraph) -> dgraph


{- returns all edges that go directly in the given node,
   in case of a DGRef node also all ingoing edges of the referenced node
   are returned -}
getAllIngoingEdges :: LibEnv -> LibNode -> [LibLEdge]
getAllIngoingEdges libEnv (ln,node) =
  case isDGRef nodelab of
    False -> inEdgesInThisGraph
    True -> inEdgesInThisGraph ++ inEdgesInRefGraph

  where 
    dgraph = lookupDGraphInLibEnv ln libEnv
    nodelab = lab' (context dgraph node)
    inEdgesInThisGraph = [(ln,inEdge)| inEdge <- inn dgraph node]
    refLn = dgn_libname nodelab
    refGraph = lookupDGraphInLibEnv refLn libEnv
    refNode = dgn_node nodelab
    inEdgesInRefGraph = [(refLn,inEdge)| inEdge <- inn refGraph refNode]


-- removes all edges that are not of the given types
filterByTypes_new :: (LEdge DGLinkLab -> Bool) -> [LibLEdge] -> [LibLEdge]
filterByTypes_new p = filter (p . snd) 

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

-- --------------------------------------------------------
-- further methods
-- -------------------------------------------------------

-- | Calculate the morphism of a path with given start node
calculateMorphismOfPathWithStart :: LibEnv -> (LibNode,[LibLEdge]) 
                                           -> Maybe GMorphism
calculateMorphismOfPathWithStart libEnv ((ln,n),[]) = do
  let dg = lookupDGraphInLibEnv ln libEnv
  ctx <- fst $ match n dg
  case getDGNode libEnv dg (fst (labNode' ctx)) of
    Just dgNode_ctx -> return $ ide Grothendieck (dgn_sign (snd (dgNode_ctx))) -- ??? to simplistic 
    Nothing -> Nothing
  
calculateMorphismOfPathWithStart _ (_,p) =
    calculateMorphismOfPath (map snd p)


-- | Compute the theory of a node (CASL Reference Manual, p. 294, Def. 4.9)
computeTheory :: LibEnv -> LIB_NAME -> DGraph -> Node -> Result G_theory 
computeTheory libEnv ln dg n = do
  let nodeLab = lab' $ context dg n
      paths = getAllGlobDefPathsBeginningWithTypesTo_new isLocalDef libEnv (ln,n) []
      -- remove emtpy path (to current node)
      paths1 = filter (not . null . snd) paths
         -- reverse needed to have a "bottom up" ordering
  mors <- maybeToMonad "Could not calculate morphism of path"
            $ mapM (calculateMorphismOfPathWithStart libEnv) paths1
  ths <- maybeToMonad "Could not calculate sentence list of node"
            $ mapM (computeLocalTheory libEnv . fst) paths1
  ths' <- mapM (uncurry translateG_theory) $ zip mors ths
  -- turn all imported theorems into axioms
  let ths'' = map (\(G_theory lid sign sens) ->
                      G_theory lid sign (map (\x -> x{isAxiom=True}) sens) ) ths'
  -- only local theory is kept with aioms and theorems
  localTh <- maybeToResult nullRange "Statc.DGToSpec.computeTheory: this cannot happen" 
             $ toG_theory (dgn_sign nodeLab) (dgn_sens nodeLab)
  th'' <- flatG_theories  (localTh:ths'')
  return (nubG_theory th'')
