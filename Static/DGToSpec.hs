{-| 
   
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
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
import Syntax.AS_Structured
import Common.AS_Annotation
import Common.Result
import Common.Id
import Common.Lib.Graph
import qualified Common.Lib.Map as Map

emptyAnno :: SPEC -> Annoted SPEC
emptyAnno x = Annoted x [] [] []

dgToSpec :: DGraph -> Node -> Result SPEC
dgToSpec dg node = do
  let (_,_,n,preds) = context node dg
  predSps <- sequence (map (dgToSpec dg . snd) preds)
  let apredSps = map emptyAnno predSps
      pos = map (\_ -> nullPos) predSps
  case n of
    (DGNode _ (G_sign lid1 sigma) (G_l_sentence_list lid2 sen) DGBasic) -> 
      do sen' <- rcoerce lid1 lid2 nullPos sen
         let b = Basic_spec (G_basic_spec lid1 (sign_to_basic_spec lid1 sigma sen'))
         if null apredSps
          then return b
          else return (Extension (apredSps++[emptyAnno b]) pos)
    (DGNode _ _ _ DGExtension) ->
         return (Extension apredSps pos)
    (DGNode _ _ _ DGUnion) ->
         return (Union apredSps pos)
    (DGNode _ _ _ DGTranslation) ->
         return (Translation (head apredSps) (Renaming [] []))
    (DGNode _ _ _ DGHiding) ->
         return (Reduction (head apredSps) (Hidden [] []))
    (DGNode _ _ _ DGRevealing) ->
         return (Reduction (head apredSps) (Hidden [] []))
    (DGNode _ _ _ DGFree) ->
         return (Free_spec (head apredSps) pos)
    (DGNode _ _ _ DGCofree) ->
         return (Cofree_spec (head apredSps) pos)
    (DGNode _ _ _ (DGSpecInst name)) ->
         return (Spec_inst name [] pos)
    (DGRef (Just name) _ _) -> return (Spec_inst name [] pos)
    _ -> return (Extension apredSps pos)

{- compute the theory of a given node. 
   If this node is a DGRef, the referenced node is looked up first. -}
computeLocalTheory :: LibEnv -> DGraph -> Node -> Maybe G_theory
computeLocalTheory libEnv dgraph node =
  if isDGRef nodeLab
    then case Map.lookup (dgn_libname nodeLab) libEnv of
      Just (_,_,refDgraph) -> 
          computeLocalTheory libEnv refDgraph (dgn_node nodeLab)
      Nothing -> Nothing
    else toG_theory (dgn_sign nodeLab) (dgn_sens nodeLab)
    where nodeLab = lab' (context node dgraph)


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
  where contextOfNode = (context node dgraph)
        nodeLab = lab' contextOfNode

getAllGlobDefPathsBeginningWithTypesTo :: [LEdge DGLinkLab -> Bool] -> DGraph 
                                       -> Node -> [LEdge DGLinkLab]
			               -> [(Node, [LEdge DGLinkLab])]
getAllGlobDefPathsBeginningWithTypesTo types dgraph node path =
  (node,path):(typeGlobPaths ++
    (concat ( [getAllGlobDefPathsBeginningWithTypesTo
                   types dgraph (getSourceNode edge) p |
                       (_, p@(edge:_)) <- globalPaths])
    )
   )

  where
    inEdges = inn dgraph node
    globalEdges = [edge| edge <- filter isGlobalDef inEdges, notElem edge path]
    edgesOfTypes 
        = [edge| edge <- filterByTypes types inEdges, notElem edge path]
    globalPaths = [(getSourceNode edge, (edge:path))| edge <- globalEdges]
    typeGlobPaths = [(getSourceNode edge, (edge:path))| edge <- edgesOfTypes]


-- removes all edges that are not of the given types
filterByTypes :: [LEdge DGLinkLab -> Bool] -> [LEdge DGLinkLab]
	      -> [LEdge DGLinkLab]
filterByTypes [] _edges = []
filterByTypes (isType:typeChecks) edgs =
  (filter isType edgs)++(filterByTypes typeChecks edgs)


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
calculateMorphismOfPathWithStart :: DGraph -> LibEnv 
                                    -> (Node,[LEdge DGLinkLab]) 
                                           -> Maybe GMorphism
calculateMorphismOfPathWithStart dg libEnv (n,[]) = do
  ctx <- fst $ match n dg
  case getDGNode libEnv dg (fst (labNode' ctx)) of
    Just dgNode_ctx -> return $ ide Grothendieck (dgn_sign (snd (dgNode_ctx))) -- ??? to simplistic 
    Nothing -> Nothing
  
calculateMorphismOfPathWithStart _ _ (_,p) = calculateMorphismOfPath p

{- returns a list of all paths to the given node
   that consist of globalDef edges only
   or
   that consist of a localDef edge followed by any number of globalDef edges -}
getAllLocGlobDefPathsTo :: DGraph -> Node -> [LEdge DGLinkLab]
			      -> [(Node, [LEdge DGLinkLab])]
getAllLocGlobDefPathsTo = getAllGlobDefPathsBeginningWithTypesTo 
			      ([isLocalDef]::[LEdge DGLinkLab -> Bool])

-- | Compute the theory of a node (CASL Reference Manual, p. 294, Def. 4.9)
computeTheory :: LibEnv -> DGraph -> Node -> Result G_theory 
computeTheory libEnv dg n = do
  let  paths = reverse $ getAllLocGlobDefPathsTo dg n []
         -- reverse needed to have a "bottom up" ordering
  mors <- maybeToMonad "Could not calculate morphism of path"
            $ mapM (calculateMorphismOfPathWithStart dg libEnv) paths
  ths <- maybeToMonad "Could not calculate sentence list of node"
            $ mapM (computeLocalTheory libEnv dg . fst) paths
  ths' <- mapM (uncurry translateG_theory) $ zip mors ths
  th'' <- maybeToMonad "Logic mismatch for theories" $ flatG_theories ths'
  return (nubG_theory th'')
