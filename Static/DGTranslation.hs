{- |
Module      :  $Header$
Copyright   :  Heng Jiang, Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  jiang@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)
Description :  Translation of development graphs along comorphisms

   Follows Sect. IV:4.3 of the CASL Reference Manual.
-}

module Static.DGTranslation (libEnv_translation, dg_translation,showFromTo) where

import Logic.Logic
import Logic.Coerce
import Logic.Comorphism
import Logic.Grothendieck
import Logic.Prover
import Syntax.AS_Library
import Static.DevGraph

import qualified Common.Lib.Map as Map
import qualified List as List (nub)
import Common.Result
import Maybe
import Data.Graph.Inductive.Graph
import Control.Exception
import Debug.Trace
import Common.DocUtils
-- import Common.AS_Annotation

-- | translation of a LibEnv (a map of globalcontext)
libEnv_translation :: LibEnv -> AnyComorphism -> Result LibEnv
libEnv_translation libEnv comorphism =
     updateGc (Map.keys libEnv) libEnv []

   where updateGc :: [LIB_NAME] -> LibEnv -> [Diagnosis] -> Result LibEnv
         updateGc [] le diag =  Result diag (Just le)
         updateGc (k1:kr) le diagnosis = 
             let gc = lookupGlobalContext k1 le
                 Result diagTran gc' = dg_translation gc comorphism
             in  updateGc kr (Map.update (\_ -> gc') k1 le) 
                     (diagnosis ++ diagTran)

dg_translation :: GlobalContext -> AnyComorphism -> Result GlobalContext
dg_translation  gc acm@(Comorphism cidMor) =
    let labNodesList = labNodes $ devGraph gc
        labEdgesList = labEdges $ devGraph gc
    in do
        resOfEdges <- mapR updateEdges labEdgesList
        resOfNodes <- mapR updateNodes labNodesList
        return gc{devGraph= mkGraph resOfNodes resOfEdges}

 where
 slid = sourceLogic cidMor
 tlid = targetLogic cidMor

 updateEdges :: LEdge DGLinkLab -> Result (LEdge DGLinkLab) 
 updateEdges 
       (from,to,(links@(DGLink { dgl_morphism= gm@(GMorphism cid' lsign ind1 lmorphism ind2)}))) =
  if isHomogeneous gm 
   then
    let sourceLid = sourceLogic cid'
        targetLid = targetLogic cid'
    in if (lessSublogicComor (sublogicOfSign (G_sign sourceLid lsign ind1)) acm) 
             && (lessSublogicComor (sublogicOfMor (G_morphism targetLid 
                                                       lmorphism ind2)) acm)
        then
            do -- translate sign of GMorphism
               (lsign', _) <- fSign sourceLid lsign
               -- translate morphism of GMorphism
               lmorphism'  <- fMor targetLid lmorphism
               -- build a new GMorphism of an edge
               case idComorphism (Logic tlid) of
                 Comorphism cid2 ->
                   let newSign = fromJust $ coerceSign tlid 
                                  (sourceLogic cid2) "DGTranslation.updateEdges" 
                                  lsign'
                       newMor = fromJust $ coerceMorphism tlid 
                                  (targetLogic cid2) "DGTranslation.updateEdges" 
                                  lmorphism'
                       slNewSign = sublogicOfSign $ 
                                    G_sign (sourceLogic cid2) 
                                      newSign ind1
                       domMor = sublogicOfSign $
                                   G_sign (targetLogic cid2) 
                                     (dom (targetLogic cid2) newMor) ind2
                   in trace (if False then 
                                 ("old:\n" ++ showDoc lsign "\nnew:\n" ++ showDoc newSign "\n\n")
                               else "") $ 
                       return $ assert (slNewSign == domMor) $ 
                             (from, to, 
                                  links{dgl_morphism= GMorphism cid2 
                                                        newSign ind1 newMor ind2
                                       }
                             )
                             
        else Result [mkDiag Error ("the sublogic of GMorphism :\""++ 
                        (show (sublogicOfMor (G_morphism targetLid lmorphism ind2))) 
                        ++ " of edge " ++ (showFromTo from to gc) 
                        ++ " is not less than " ++ (show acm )) ()] (Nothing)
     else Result [mkDiag Error ("Link "++ (showFromTo from to gc) ++ 
                                " is not homogeneous.") ()]
          (Nothing)

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
     coerceSign sourceID slid "DGTranslation.fSign" sign >>=
        map_sign cidMor

 fTh _ (G_theory lid sign _ thSens _) = do
   -- (sign', _) <- fSign lid sign 
   sign' <- coerceSign lid slid "DGTranslation.fTh.sign" sign 
   thSens' <- coerceThSens lid slid "DGTranslation.fTh.sen" thSens
{-
   namedList <- mapM (\nt -> case nt of 
                 NamedSen p1 p2 p3 s -> 
                     do ns <- map_sentence cidMor sign s
                        return (NamedSen p1 p2 p3 ns)) (toNamedList thSens')
-}  
   (sign'', namedS) <- map_theory cidMor (sign', toNamedList thSens')
   let th = G_theory tlid sign'' 0 (toThSens $ List.nub namedS) 0
--   let th = G_theory tlid sign' (toThSens $ List.nub namedList)
   return th


 fMor sourceID mor =
     coerceMorphism sourceID slid "DGTranslation.fMor" mor >>=
                    map_morphism cidMor


-- | get the name of a node from the number of node
getNameOfNode :: Node -> GlobalContext -> String
getNameOfNode index gc =
     let (_, _, node, _) = fromJust $ fst $ match index $ devGraph $ gc
     in  getDGNodeName node

showFromTo :: Node -> Node -> GlobalContext -> String
showFromTo from to gc =
    "from " ++ (getNameOfNode from gc) ++ " to " ++ (getNameOfNode to gc)