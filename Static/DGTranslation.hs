{- |
Module      :  $Header$
Description :  Translation of development graphs along comorphisms
Copyright   :  Heng Jiang, Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  jiang@informatik.uni-bremen.de
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

import Logic.Logic
import Logic.Coerce
import Logic.Comorphism
import Logic.Grothendieck
import Logic.Prover

import Common.ExtSign
import Common.LibName
import Common.Result

import qualified Data.Map as Map
import qualified Data.List as List (nub)
import Data.Maybe
import Data.Graph.Inductive.Graph
import Control.Exception

-- | translation of a LibEnv (a map of globalcontext)
libEnv_translation :: LibEnv -> AnyComorphism -> Result LibEnv
libEnv_translation libEnv comorphism =
     updateGc (Map.keys libEnv) libEnv []

   where updateGc :: [LibName] -> LibEnv -> [Diagnosis] -> Result LibEnv
         updateGc [] le diag =  Result diag (Just le)
         updateGc (k1:kr) le diagnosis =
             let gc = lookupDGraph k1 le
                 Result diagTran gc' = dg_translation gc comorphism
             in  updateGc kr (Map.update (const gc') k1 le)
                     (diagnosis ++ diagTran)

dg_translation :: DGraph -> AnyComorphism -> Result DGraph
dg_translation  gc acm@(Comorphism cidMor) =
    let labNodesList = labNodesDG gc
        labEdgesList = labEdgesDG gc
    in addErrorDiag ("translation failed via: " ++ language_name cidMor) ()
       $ do
        resOfEdges <- mapR updateEdges labEdgesList
        resOfNodes <- mapR updateNodes labNodesList
        return $ mkGraphDG resOfNodes resOfEdges emptyDG

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

 updateNodes :: LNode DGNodeLab -> Result (LNode DGNodeLab)
 updateNodes (node, dgNodeLab) =
     case fTh node $ dgn_theory dgNodeLab of
       Result diagsT maybeTh ->
           maybe (Result diagsT Nothing)
              (\th' -> Result diagsT
                       (Just (node, dgNodeLab {dgn_theory = th'
                                              ,dgn_nf = Nothing
                                              ,dgn_sigma = Nothing
                                              }))) maybeTh

 -- !! the sign from fSign and from fTh maybe different.
 -- to translate sign
 fSign sourceID sign =
     coercePlainSign sourceID slid "DGTranslation.fSign" sign >>=
        map_sign cidMor

 fTh _ (G_theory lid sign _ thSens _) = do
   -- (sign', _) <- fSign lid sign
   (ExtSign sign' _) <-
       coerceSign lid slid "DGTranslation.fTh.sign" sign
   thSens' <- coerceThSens lid slid "DGTranslation.fTh.sen" thSens
   (sign'', namedS) <- wrapMapTheory cidMor (sign', toNamedList thSens')
   return $ G_theory tlid (mkExtSign sign'') startSigId
              (toThSens $ List.nub namedS) startThId

 fMor sourceID mor =
     coerceMorphism sourceID slid "DGTranslation.fMor" mor >>=
                    map_morphism cidMor

showFromTo :: Node -> Node -> DGraph -> String
showFromTo from to gc =
    "from " ++ getNameOfNode from gc ++ " to " ++ getNameOfNode to gc

-- | get the maximal sublogic of a graph.
-- | each DGraph and each node will be tested, in order to find
-- | the maximal sublogic of th Graph.
-- | All edges and nodes will be searched also in the meantime, so as to test,
-- | whether the GMorphism of edges is homogeneous, and the logics of nodes are
-- | equal.
getDGLogic :: LibEnv -> Result G_sublogics
getDGLogic libEnv =
    let sublogicsMap = map (getSublogicFromDGraph libEnv)
                           (Map.keys libEnv)
    in  foldr comResSublogics (Result [] Nothing) sublogicsMap

getSublogicFromDGraph :: LibEnv -> LibName -> Result G_sublogics
getSublogicFromDGraph le ln =
    let edgesList = labEdgesDG gc
        nodesList = labNodesDG gc
        slList1   = map testAndGetSublogicFromEdge edgesList
        slList2   = map (getSubLogicsFromNodes $ getFirstLogic nodesList)
                        nodesList
    in  foldr comResSublogics (Result [] Nothing) (slList1 ++ slList2)

  where
    gc = lookupDGraph ln le

    testAndGetSublogicFromEdge :: LEdge DGLinkLab -> Result G_sublogics
    testAndGetSublogicFromEdge l@(_, _,
             DGLink gm@(GMorphism cid' (ExtSign lsign _) _ lmorphism _) _ _ _)
        =
          if isHomogeneous gm then
              Result [] (joinSublogics g_mor g_sign)
              else Result [mkDiag Error
                           ("the " ++ showLEdge l ++
                            " is not homogeneous.") () ] Nothing

         where g_mor = G_sublogics (targetLogic cid') $ minSublogic lmorphism
               g_sign = G_sublogics (sourceLogic cid') $ minSublogic lsign


    getSubLogicsFromNodes :: AnyLogic -> LNode DGNodeLab
                          -> Result G_sublogics
    getSubLogicsFromNodes logic (_, lnode) =
        case dgn_theory lnode of
          th@(G_theory lid _ _ _ _) ->
              if Logic lid == logic then
                  Result [] (Just $ sublogicOfTh th)
                 else Result [mkDiag Error
                              ("the node " ++ getDGNodeName lnode ++
                               "  has a different logic \"" ++ show lid ++
                               "\" as the logic of Graph \"" ++ show logic ++
                               " is not homogeneous.") () ] Nothing

    getFirstLogic :: [LNode DGNodeLab] -> AnyLogic
    getFirstLogic list =
        case dgn_theory $ snd $ head list of
          G_theory lid _ _ _ _ ->
              Logic lid


comResSublogics :: Result G_sublogics
                -> Result G_sublogics
                -> Result G_sublogics
comResSublogics (Result diags1 msubl1@(Just subl1))
                    (Result diags2 msubl2) =
               case msubl2 of
                 Nothing -> Result (diags1 ++ diags2) msubl1
                 Just subl2 ->
                     Result (diags1 ++ diags2) $ joinSublogics subl1 subl2
comResSublogics (Result diags1 Nothing) (Result diags2 _) =
    Result (diags1 ++ diags2) Nothing

