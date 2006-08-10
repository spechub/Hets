{- |
Module      :  $Header$
Copyright   :  Heng Jiang, Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Central data structure for development graphs.
   Follows Sect. IV:4.2 of the CASL Reference Manual.
-}

module Static.DGTranslation (libEnv_translation, dg_translation) where

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
-- import Common.Id
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
 
-- | translation a GlobalContext on the basis the given Comorphism 
-- | if the sublogic of (theory of) node less than given Comorphism
-- | then call the process to translate;
-- | otherwise do not translate the graph. 
dg_translation :: GlobalContext -> AnyComorphism -> Result GlobalContext
dg_translation gc cm = 
    let nodesList = nodes $ devGraph gc
    in  mainTrans nodesList [] gc
  where  
    -- rekursiv translate alle nodes of DevGraph of GlobalContext
    mainTrans [] diagsMain gcon = Result diagsMain (Just gcon)
    mainTrans (h:r) diagsMain gcon  =  
        case fst $ match h $ devGraph gcon of
          Just (_, _, nodeLab, _) ->
           -- if the sublogic of (theory of) node less than given Comorphism
           -- then call the process to translate;
           -- otherwise do not translate the graph.
           if lessSublogicComor 
                  (sublogicOfTh $ dgn_theory nodeLab)  cm
              then let Result diags' maybeGC = updateNode h gcon cm 
                   in case maybeGC of
                         Just gc' -> mainTrans r (diagsMain ++ diags') gc'  
                         Nothing -> mainTrans r (diagsMain ++ diags') gcon 
              else let nodeName = getDGNodeName nodeLab
                       slOfNode = sublogicOfTh $ dgn_theory nodeLab
                       hintDiag = [(mkDiag Error ("sublogic of " ++ 
                                    nodeName ++ " is " ++ show slOfNode ++
                                    ", this is not less than " ++ (show cm))
                                    ())] 
		   in  mainTrans r (diagsMain++hintDiag) gcon
          Nothing -> mainTrans r (diagsMain ++ 
                                  [(mkDiag Error ("node " ++ (show h) 
                              ++ " is not found in graph.") ())]) gcon

-- | update the translated node	
updateNode :: Node    -- ^ the number of node
           -> GlobalContext -> AnyComorphism -> Result GlobalContext
updateNode index gc acm@(Comorphism cidMor) =
    let (inLinks, _, node, _) = 
            fromJust $ fst $ match index  $ devGraph gc
        Result diagsL m_dgWithNewEdges =
             updateEdges inLinks [] (devGraph gc)
    in 
        case m_dgWithNewEdges of
         Just dgWithNewEdges ->
           let  Result diagsN m_dgAll = transTh node dgWithNewEdges
           in 
             case m_dgAll of
               Just dgAll -> 
                   Result (diagsN ++ diagsL)
                              (Just (gc {devGraph=dgAll}))
               Nothing ->
                   Result (diagsN ++ diagsL ++ 
                               [mkDiag Error "translation of nodes failed." ()])
                              (Just gc)         -- Nothing?
         Nothing -> Result (diagsL ++
                                [mkDiag Error "translation of edges failed." ()])
                      (Just gc)        -- Nothing?
      

   where 
     slid = sourceLogic cidMor
     tlid = targetLogic cidMor


     -- update the edges of a node
     -- if the sublogic of (sign and morphism of) node less than given 
     -- Comorphism then translate the GMorphism, otherwise give out a
     -- Error-Diagnosis, but the GMorphism is not translated.
     updateEdges :: [(DGLinkLab,Node)] -> [Diagnosis] -> DGraph 
                -> Result DGraph
     updateEdges [] diagsAll dGraph = Result diagsAll $ Just dGraph
     updateEdges ((links@(DGLink gm@(GMorphism cid' lsign lmorphism) _ _),n):r) 
                 diagnosis dGraph =
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
                                           G_sign (targetLogic cid2) (dom (targetLogic cid2) newMor)
                            in  assert (slNewSign == domMor) $ 
                                updateEdges r  
                                 (diagnosis ++ diagLs ++ diagLm ++ 
                                  [mkDiag Hint 
                                   ((getNameOfNode n gc) ++ "->" ++ (getNameOfNode index gc) ++ ":\n\tSign    :  " ++ (show $ sublogicOfSign (G_sign sourceLid lsign)) ++ " --> " ++ (show slNewSign) ++ "\n\tMorphism:  " ++ (show $ sublogicOfMor (G_morphism targetLid lmorphism)) ++ " --> " ++ (show slNewMor)) () ] )
                                 (emap (\x -> if x == links then links{
                                                        dgl_morphism= 
                                                             GMorphism cid2 
                                                               newSign newMor
                                                                      }
                                                else x) dGraph)
                       Result diagLm Nothing  ->  Result (diagLm ++ 
                         [mkDiag Error 
                          ("morphism of link can not be translated.") ()]) 
                         (Just dGraph)
                   Result diagLs Nothing  -> Result (diagLs ++ 
                         [mkDiag Error 
                          ("sign of link can not be translated.") ()]) 
                         (Just dGraph)
               else Result [mkDiag Error ("GMorphism of a Link to node " ++ 
                                         (getNameOfNode n gc) ++ 
                                         " is not less than ." ++ 
                                         (show cidMor)) ()] 
                        (Just dGraph)
          else Result [mkDiag Error ("Link is not homogeneous.") ()] 
                     (Just dGraph)         
              
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
        Nothing  -> Result [mkDiag Error ("cannot coerce sign" ++ showDoc sign "\n")
                            ()] Nothing 

     -- to translate theory
     transTh node gcWithNewEdges =
          case fTh $ dgn_theory node of
           Result diagsT maybeTh -> 
               case maybeTh of
                 Just th' -> 
                       Result diagsT (Just (nmap (\x -> if x == node then 
                                                          node {dgn_theory = th'
                                                               ,dgn_nf = Nothing
                                                               ,dgn_sigma = Nothing
                                                               } 
                                                        else x) gcWithNewEdges)) 
                 Nothing  -> Result diagsT Nothing

     fTh g@(G_theory lid sign thSens) =
      case coerceSign lid slid "" sign of
        Just sign' -> 
            case coerceThSens lid slid "" thSens of
              Just thSens' -> 
                  case map_theory cidMor (sign', toNamedList thSens') of
                    Result diagsOfth maybeTh ->
                      case maybeTh of
                        Just (sign'', namedS) -> 
                          let th = G_theory tlid sign'' (toThSens $ List.nub namedS)
                              diagTrans = mkDiag Hint 
                                          ("\n" ++ (getNameOfNode index gc) ++ ": " 
                                           ++ (show $ sublogicOfTh g) ++ " -> " 
                                           ++ (show $ sublogicOfTh th)) ()
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
