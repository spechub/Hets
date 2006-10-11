{- |
Module      :  $Header$
Copyright   :  Heng Jiang, Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Central data structure for development graphs.
   Follows Sect. IV:4.2 of the CASL Reference Manual.
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
-- import Debug.Trace
import Common.DocUtils

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
    in case mapR updateEdges labEdgesList of
         Result diagsFromEdges (Just resOfEdges) ->
             if hasErrors diagsFromEdges then
                 Result diagsFromEdges (Just gc)    -- Nothing?
               else
                  case mapR updateNodes labNodesList of
                    Result diagsFromNodes (Just resOfNodes) ->
                        if hasErrors diagsFromNodes then
                            Result (diagsFromEdges ++ diagsFromNodes) (Just gc)
                          else
                              Result (diagsFromEdges ++ diagsFromNodes)
                                     (Just gc{devGraph=
                                              mkGraph resOfNodes resOfEdges })
                    Result diagsFromNodes Nothing ->
                        -- remove warning
                        Result (diagsFromEdges ++ diagsFromNodes) (Just gc)
         Result diagsFromEdges Nothing ->
             -- remove warning
             Result diagsFromEdges (Just gc) 

 where
 slid = sourceLogic cidMor
 tlid = targetLogic cidMor

 updateEdges :: LEdge DGLinkLab -> Result (LEdge DGLinkLab) 
 updateEdges 
       ledge@(from,to,(links@(DGLink gm@(GMorphism cid' lsign lmorphism) _ _)))=
  if isHomogeneous gm 
   then
    let sourceLid = sourceLogic cid'
        targetLid = targetLogic cid'
    in if (lessSublogicComor (sublogicOfSign (G_sign sourceLid lsign)) acm) 
             && (lessSublogicComor (sublogicOfMor (G_morphism targetLid 
                                                       lmorphism)) acm)
        then
           -- translate sign of GMorphism
           case fSign sourceLid lsign of
             Result diagLs (Just (lsign', _)) -> 
              -- translate morphism of GMorphism
              case fMor targetLid lmorphism of
                Result diagLm (Just lmorphism') -> 
                  -- build a new GMorphism of an edge
                  case idComorphism (Logic tlid) of 
                    Comorphism cid2 ->
                      let newSign = fromJust $ coerceSign tlid 
                                    (sourceLogic cid2) "" lsign'
                          newMor = fromJust $ coerceMorphism tlid 
                                   (targetLogic cid2) "" lmorphism'
                          slNewSign = sublogicOfSign $ 
                                                 G_sign (sourceLogic cid2) 
                                                        newSign
                          slNewMor = sublogicOfMor $ 
                                          G_morphism (targetLogic cid2) 
                                                     newMor     
                          domMor = sublogicOfSign $
                                          G_sign (targetLogic cid2) 
                                                 (dom (targetLogic cid2) newMor)
                      in  assert (slNewSign == domMor) $ 
                          Result (diagLs ++ diagLm ++ 
                              [mkDiag Hint 
                               ((getNameOfNode from gc) ++ "->" ++ 
                                (getNameOfNode to gc) ++ ":\n\tSign    :  " ++ 
                                (show $ sublogicOfSign (G_sign sourceLid lsign)) 
                                ++ " --> " ++ (show slNewSign) ++ 
                                "\n\tMorphism:  " ++ (show $ sublogicOfMor 
                                   (G_morphism targetLid lmorphism)) ++ 
                                " --> " ++ (show slNewMor)) () ])
                             (Just (from, to, 
                                        links{dgl_morphism= GMorphism cid2 
                                                            newSign newMor
                                             }
                                   )
                             )
                Result diagLm Nothing  -> 
                    Result (diagLm ++ 
                            [mkDiag Error 
                                ("morphism of link " ++ (showFromTo from to gc)
                                 ++ " can not be translated.") ()]) 
                            (Just ledge)
             Result diagLs Nothing  -> 
                 Result (diagLs ++ 
                         [mkDiag Error 
                          ("sign of link " ++ (showFromTo from to gc) ++
                                               " can not be translated.")
                          ()]) (Just ledge) 
          else Result [mkDiag Error ("the sublogic of GMorphism :\""++ 
                        (show (sublogicOfMor (G_morphism targetLid lmorphism))) 
                        ++ " of edge " ++ (showFromTo from to gc) 
                        ++ " is not less than " ++ (show acm )) ()] (Just ledge)
     else Result [mkDiag Error ("Link "++ (showFromTo from to gc) ++ 
                                " is not homogeneous.") ()]
          (Just ledge)

 updateNodes :: LNode DGNodeLab -> Result (LNode DGNodeLab) 
 updateNodes lNode@(node, dgNodeLab) =
     case fTh node $ dgn_theory dgNodeLab of
       Result diagsT maybeTh ->
           maybe (Result diagsT (Just lNode)) 
              (\th' -> Result diagsT (Just (node, dgNodeLab {dgn_theory = th'
                                                            ,dgn_nf = Nothing
                                                            ,dgn_sigma = Nothing
                                                            }))) maybeTh

 -- to translate sign
 fSign sourceID sign =
      case coerceSign sourceID slid "" sign of
        Just sign' -> 
            case map_sign cidMor sign' of
              Result diagsOfcs maybeSign ->
                  case maybeSign of
                    Just (sign'', sens) ->
                        Result diagsOfcs 
                               (Just (sign'',sens))
                    Nothing -> error "Result diagsOfcs Nothing"
        Nothing  -> Result [mkDiag Error ("cannot coerce sign" ++ 
                                          showDoc sign "\n")
                            ()] Nothing 

 fTh node g@(G_theory lid sign thSens) =
      case coerceSign lid slid "" sign of
        Just sign' -> 
            case coerceThSens lid slid "" thSens of
              Just thSens' -> 
                  case map_theory cidMor (sign', toNamedList thSens') of
                    Result diagsOfth maybeTh ->
                      case maybeTh of
                        Just (sign'', namedS) -> 
                          let th = G_theory tlid sign'' 
                                            (toThSens $ List.nub namedS)
                              diagTrans = mkDiag Hint 
                                          ("\n" ++ (getNameOfNode node gc) ++ 
                                           ": " ++ (show $ sublogicOfTh g) ++ 
                                           " -> " ++ (show $ sublogicOfTh th)) ()
                          in Result (diagsOfth ++ [diagTrans]) (Just th)
                        Nothing ->  error "Result diagsOfth Nothing"
              Nothing    -> Result [(mkDiag Error 
                                     ("cannot coerce sens" ++ show thSens)
                                     ())] Nothing 
        Nothing -> Result [(mkDiag Error ("cannot coerce sign" ++ show sign)
                                     ())] Nothing 

 fMor sourceID mor =
        case coerceMorphism sourceID slid "" mor of
          Just mor' -> 
              let Result diagsM res =  map_morphism cidMor mor'
              in  Result diagsM res
          Nothing -> Result [(mkDiag Error ("cannot coerce mor" ++ show mor)
                              ())] Nothing  

-- | get the name of a node from the number of node
getNameOfNode :: Node -> GlobalContext -> String
getNameOfNode index gc =
     let (_, _, node, _) = fromJust $ fst $ match index $ devGraph $ gc
     in  getDGNodeName node

showFromTo :: Node -> Node -> GlobalContext -> String
showFromTo from to gc =
    "from " ++ (getNameOfNode from gc) ++ " to " ++ (getNameOfNode to gc)