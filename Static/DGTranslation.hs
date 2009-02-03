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
    ) where

import Static.GTheory
import Static.DevGraph

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

   where updateGc :: [LIB_NAME] -> LibEnv -> [Diagnosis] -> Result LibEnv
         updateGc [] le diag =  Result diag (Just le)
         updateGc (k1:kr) le diagnosis =
             let gc = lookupDGraph k1 le
                 Result diagTran gc' = dg_translation gc comorphism
             in  updateGc kr (Map.update (\_ -> gc') k1 le)
                     (diagnosis ++ diagTran)

dg_translation :: DGraph -> AnyComorphism -> Result DGraph
dg_translation  gc acm@(Comorphism cidMor) =
    let labNodesList = labNodesDG gc
        labEdgesList = labEdgesDG gc
    in do
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
                       return $ assert (slNewSign == domMor) $
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
           maybe (Result diagsT (Nothing))
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
