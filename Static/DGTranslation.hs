{- |
Module      :  ./Static/DGTranslation.hs
Description :  Translation of development graphs along comorphisms
Copyright   :  Heng Jiang, Uni Bremen 2004-2006
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

Translation of development graphs along comorphisms
   Follows Sect. IV:4.3 of the CASL Reference Manual.
-}

module Static.DGTranslation
    ( libEnv_translation
    , dg_translation
    , getDGLogic
    ) where

import Static.GTheory
import Static.DevGraph
import Static.PrintDevGraph
import Static.ComputeTheory

import Logic.Logic
import Logic.Coerce
import Logic.Comorphism
import Logic.Grothendieck
import Logic.Prover

import Common.ExtSign
import Common.LibName
import Common.Result

import qualified Data.HashMap.Strict as Map
import qualified Data.HashSet as Set

import Data.Graph.Inductive.Graph

import Control.Monad (foldM)

-- | translation of a LibEnv (a map of globalcontext)
libEnv_translation :: LibEnv -> AnyComorphism -> Result LibEnv
libEnv_translation libEnv com =
  foldM (\ le ln -> do
    dgTr <- dg_translation le ln (lookupDGraph ln libEnv) com
    return $ Map.insert ln dgTr le) Map.empty $ getTopsortedLibs libEnv

dg_translation :: LibEnv -> LibName -> DGraph -> AnyComorphism -> Result DGraph
dg_translation le ln gc acm@(Comorphism cidMor) =
    let labNodesList = labNodesDG gc
        labEdgesList = labEdgesDG gc
    in addErrorDiag ("translation failed via: " ++ language_name cidMor) ()
       $ do
        resOfEdges <- mapM (updateEdges acm gc) labEdgesList
        resOfNodes <- mapM (updateNodes acm) labNodesList
        return $ computeDGraphTheories le ln
          $ mkGraphDG resOfNodes resOfEdges emptyDG

updateEdges :: AnyComorphism -> DGraph -> LEdge DGLinkLab
  -> Result (LEdge DGLinkLab)
updateEdges (Comorphism cidMor) gc (s, t, lbl) = case dgl_morphism lbl of
  GMorphism cid' esig _ mor _ ->
   if isIdComorphism (Comorphism cid')
   then do
     let slid = sourceLogic cidMor
         tlid = targetLogic cidMor
     ExtSign lsign sys <- coerceSign (sourceLogic cid') slid
       "DGTranslation.fSign" esig
     (lsign', _) <- map_sign cidMor lsign
     lMor <- coerceMorphism (targetLogic cid') slid "DGTranslation.fMor" mor
     lmorphism' <- map_morphism cidMor lMor
     return (s, t, lbl
       { dgl_morphism = GMorphism (mkIdComorphism tlid $ top_sublogic tlid)
         (ExtSign lsign' $ Set.unions
         $ map (map_symbol cidMor lsign) $ Set.toList sys)
         startSigId lmorphism' startMorId })
   else fail $ "Link " ++ showFromTo s t gc ++ " is not homogeneous."

updateNodes :: AnyComorphism -> LNode DGNodeLab -> Result (LNode DGNodeLab)
updateNodes (Comorphism cidMor) (node, dgNodeLab) =
  case dgn_theory dgNodeLab of
    G_theory lid _ esig _ thSens _ -> do
      let slid = sourceLogic cidMor
      ExtSign sign' sys' <- coerceSign lid slid "DGTranslation.fTh.sign" esig
      thSens' <- coerceThSens lid slid "DGTranslation.fTh.sen" thSens
      (sign'', namedS) <- wrapMapTheory cidMor (sign', toNamedList thSens')
      return (node, dgNodeLab
        { dgn_nf = Nothing
        , dgn_sigma = Nothing
        , dgn_theory = G_theory (targetLogic cidMor) Nothing
            (ExtSign sign'' $ Set.unions
            $ map (map_symbol cidMor sign') $ Set.toList sys')
            startSigId (toThSens namedS) startThId })

showFromTo :: Node -> Node -> DGraph -> String
showFromTo from to gc =
    "from " ++ getNameOfNode from gc ++ " to " ++ getNameOfNode to gc

{- | get the maximal sublogic of a graph.
 each DGraph and each node will be tested, in order to find
 the maximal sublogic of th Graph.
 All edges and nodes will be searched also in the meantime, so as to test,
 whether the GMorphism of edges is homogeneous, and the logics of nodes are
 equal. -}
getDGLogic :: LibEnv -> Result G_sublogics
getDGLogic libEnv =
    mapM (getSublogicFromDGraph libEnv) (Map.keys libEnv)
    >>= combineSublogics

getSublogicFromDGraph :: LibEnv -> LibName -> Result G_sublogics
getSublogicFromDGraph le ln = do
    let gc = lookupDGraph ln le
        edgesList = labEdgesDG gc
        nodesList = labNodesDG gc
    slList1 <- mapM testAndGetSublogicFromEdge edgesList
    slList2 <- mapM (getSubLogicsFromNodes $ getFirstLogic nodesList)
                        nodesList
    combineSublogics $ slList1 ++ slList2

combineSublogics :: [G_sublogics] -> Result G_sublogics
combineSublogics l = case l of
  [] -> fail "Static.DGTranslation.combineSublogics.empty"
  h : t -> case foldr (\ s ms -> case ms of
           Just u -> joinSublogics s u
           _ -> Nothing) (Just h) t of
     Nothing -> fail "Static.DGTranslation.combineSublogics"
     Just s -> return s

testAndGetSublogicFromEdge :: LEdge DGLinkLab -> Result G_sublogics
testAndGetSublogicFromEdge l@(_, _, lbl) =
  case dgl_morphism lbl of
    GMorphism cid' (ExtSign lsign _) _ lmorphism _ -> do
      let tlid = targetLogic cid'
      lsign' <- coercePlainSign (sourceLogic cid') tlid
        (showLEdge l ++ " is not homogeneous.") lsign
      return $ G_sublogics tlid $ lub (minSublogic lsign' )
        $ minSublogic lmorphism

getSubLogicsFromNodes :: AnyLogic -> LNode DGNodeLab -> Result G_sublogics
getSubLogicsFromNodes logic (_, lnode) =
        case dgn_theory lnode of
          th@(G_theory lid _ _ _ _ _) ->
              if Logic lid == logic then return $ sublogicOfTh th
                 else fail $ "the node " ++ getDGNodeName lnode ++
                               "  has a different logic \"" ++ show lid ++
                               "\" as the logic of Graph \"" ++ show logic ++
                               " is not homogeneous."

getFirstLogic :: [LNode DGNodeLab] -> AnyLogic
getFirstLogic list = case list of
  (_, nlab) : _ -> case dgn_theory nlab of
          G_theory lid _ _ _ _ _ -> Logic lid
  _ -> error "Static.DGTranslation.getFirstLogic"
