{- |
Module      :  $Header$
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

import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.Maybe
import Data.Graph.Inductive.Graph

import Control.Exception
import Control.Monad (foldM)

-- | translation of a LibEnv (a map of globalcontext)
libEnv_translation :: LibEnv -> AnyComorphism -> Result LibEnv
libEnv_translation libEnv com =
  foldM (\ le ln -> do
    dgTr <- dg_translation le (lookupDGraph ln libEnv) com
    return $ Map.insert ln dgTr le) Map.empty $ getTopsortedLibs libEnv

dg_translation :: LibEnv -> DGraph -> AnyComorphism -> Result DGraph
dg_translation le gc acm@(Comorphism cidMor) =
    let labNodesList = labNodesDG gc
        labEdgesList = labEdgesDG gc
    in addErrorDiag ("translation failed via: " ++ language_name cidMor) ()
       $ do
        resOfEdges <- mapR updateEdges labEdgesList
        resOfNodes <- mapR (updateNodes acm) labNodesList
        return $ computeDGraphTheories le
          $ mkGraphDG resOfNodes resOfEdges emptyDG

 where
 slid = sourceLogic cidMor
 tlid = targetLogic cidMor

 updateEdges :: LEdge DGLinkLab -> Result (LEdge DGLinkLab)
 updateEdges
       (from,to,(links@(DGLink { dgl_morphism=
             gm@(GMorphism cid' (ExtSign lsign _) ind1 lmorphism ind2)}))) =
  if isHomogeneous gm
   then
    let sourceLid = sourceLogic cid'
        targetLid = targetLogic cid'
        minTargetSublogic = G_sublogics targetLid $ minSublogic lmorphism
    in if lessSublogicComor (G_sublogics sourceLid $ minSublogic lsign) acm
        && lessSublogicComor minTargetSublogic acm
        then
            do -- translate sign of GMorphism
               (lsign', _) <- fSign sourceLid lsign
               -- translate morphism of GMorphism
               lmorphism'  <- fMor targetLid lmorphism
               -- build a new GMorphism of an edge
               case idComorphism (Logic tlid) of
                 Comorphism cid2 ->
                   let newSign = fromJust $ coercePlainSign tlid
                         (sourceLogic cid2) "DGTranslation.updateEdges"
                                  lsign'
                       newMor = fromJust $ coerceMorphism tlid
                          (targetLogic cid2) "DGTranslation.updateEdges"
                                  lmorphism'
                       slNewSign = G_sublogics (sourceLogic cid2)
                                   $ minSublogic newSign
                       targetLogic2 = targetLogic cid2
                       domMor = G_sublogics targetLogic2
                                   $ minSublogic $ dom newMor
                   in
-- ("old:\n" ++ showDoc lsign "\nnew:\n" ++ showDoc newSign "\n\n")
                       return $ assert (slNewSign == domMor)
                             (from, to,
                                  links{dgl_morphism= GMorphism cid2
                                         (mkExtSign newSign)
                                         ind1 newMor ind2
                                       }
                             )

        else Result [mkDiag Error ("the sublogic of GMorphism :\"" ++
                     show minTargetSublogic
                     ++ " of edge " ++ showFromTo from to gc
                     ++ " is not less than " ++ show acm) ()] Nothing
     else Result [mkDiag Error ("Link "++ showFromTo from to gc ++
                                " is not homogeneous.") ()] Nothing

 -- !! the sign from fSign and from fTh maybe different.
 -- to translate sign
 fSign sourceID sign =
     coercePlainSign sourceID slid "DGTranslation.fSign" sign >>=
        map_sign cidMor

 fMor sourceID mor =
     coerceMorphism sourceID slid "DGTranslation.fMor" mor >>=
                    map_morphism cidMor

updateNodes :: AnyComorphism -> LNode DGNodeLab -> Result (LNode DGNodeLab)
updateNodes (Comorphism cidMor) (node, dgNodeLab) =
  case dgn_theory dgNodeLab of
    G_theory lid esig _ thSens _ -> do
      let slid = sourceLogic cidMor
      ExtSign sign' sys' <- coerceSign lid slid "DGTranslation.fTh.sign" esig
      thSens' <- coerceThSens lid slid "DGTranslation.fTh.sen" thSens
      (sign'', namedS) <- wrapMapTheory cidMor (sign', toNamedList thSens')
      syms <- return $ map (map_symbol cidMor sign') $ Set.toList sys'
      return (node, dgNodeLab
        { dgn_nf = Nothing
        , dgn_sigma = Nothing
        , dgn_theory = G_theory (targetLogic cidMor)
            (ExtSign sign'' $ Set.unions syms) startSigId
            (toThSens namedS) startThId })

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
    mapR (getSublogicFromDGraph libEnv) (Map.keys libEnv)
    >>= combineSublogics

getSublogicFromDGraph :: LibEnv -> LibName -> Result G_sublogics
getSublogicFromDGraph le ln = do
    let gc = lookupDGraph ln le
        edgesList = labEdgesDG gc
        nodesList = labNodesDG gc
    slList1 <- mapR testAndGetSublogicFromEdge edgesList
    slList2 <- mapR (getSubLogicsFromNodes $ getFirstLogic nodesList)
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
        (showLEdge l ++ " is not homogeneous.")  lsign
      return $ G_sublogics tlid $ join (minSublogic lsign' )
        $ minSublogic lmorphism

getSubLogicsFromNodes :: AnyLogic -> LNode DGNodeLab -> Result G_sublogics
getSubLogicsFromNodes logic (_, lnode) =
        case dgn_theory lnode of
          th@(G_theory lid _ _ _ _) ->
              if Logic lid == logic then return $ sublogicOfTh th
                 else Result [mkDiag Error
                              ("the node " ++ getDGNodeName lnode ++
                               "  has a different logic \"" ++ show lid ++
                               "\" as the logic of Graph \"" ++ show logic ++
                               " is not homogeneous.") () ] Nothing

getFirstLogic :: [LNode DGNodeLab] -> AnyLogic
getFirstLogic list = case list of
  (_, nlab) : _ -> case dgn_theory nlab of
          G_theory lid _ _ _ _ -> Logic lid
  _ -> error "Static.DGTranslation.getFirstLogic"
