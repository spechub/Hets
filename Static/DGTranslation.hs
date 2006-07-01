{- |
Module      :  $Header$
Copyright   :  Heng Jiang, Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Central data structure for development graphs.
   Follows Sect. IV:4.2 of the CASL Reference Manual.
-}

module Static.DGTranslation (dg_translation) where

import Logic.Logic
import Logic.Coerce
import Logic.Comorphism
import Logic.Grothendieck
import Logic.Prover

import Static.DevGraph
import qualified Common.Lib.Map as Map
import Common.Result
import Maybe
import Common.Lib.Graph
import Data.Graph.Inductive.Graph

-- translation between two GlobalContext on the basis the given Comorphism 
dg_translation :: GlobalContext -> AnyComorphism -> Result GlobalContext
dg_translation gc cm@(Comorphism cidMor) =
    mainTrans (Map.keys $ toMap $ devGraph gc) [] gc
  where  
        mainTrans [] diags gc = Result diags (Just gc)
        mainTrans (h:r) diags gc =  
            case Map.lookup h (toMap $ devGraph gc) of
              Just (_, nodeLab, _) ->
                  if lessSublogicComor 
                         (sublogicOfTh $ dgn_theory nodeLab) cm
                    then let Result diags' maybeGC = updateNode h gc cm 
                         in  case maybeGC of
                             Just gc' -> mainTrans r (diags ++ diags') gc'
                             Nothing -> mainTrans r (diags ++ diags') gc
                    else mainTrans r ((mkDiag Hint ("node " ++ (show h) ++
                            ":" ++ (show $ dgn_name nodeLab) ++
                            " is not less than " ++ (show cm)) ()):diags) gc
              Nothing -> mainTrans r ((mkDiag Error ("node " ++ (show h) 
                              ++ " is not found in graph.") ()):diags) gc

 

updateNode :: Int -> GlobalContext -> AnyComorphism -> Result GlobalContext
updateNode index gc cm@(Comorphism cidMor) =
    -- sigMap, thMap and morMap can be empty, so the index of node can
    -- not be found in it.
    let (inLinks, node, outLinks) = 
            fromJust $ Map.lookup index $ toMap $ devGraph gc
        Result diagsL1 newL1 = foldl (joinResultWith (\ a b -> a ++ b)) 
                               (Result [] (Just [])) (map updateEdge inLinks)
        Result diagsL2 newL2 = foldl (joinResultWith (\ a b -> a ++ b)) 
                               (Result [] (Just [])) (map updateEdge outLinks)
        Result thDiag _ = fTh $ dgn_theory node 
    in  Result (thDiag ++ diagsL1 ++ diagsL2)
                (Just (gc {devGraph=Gr (Map.update (transDev (fromJust newL1)
                                                            (fromJust newL2)) 
                                        index 
                                        (toMap $ devGraph gc))

                          }))
   where 
     slid = sourceLogic cidMor
     tlid = targetLogic cidMor

     updateEdge :: (DGLinkLab, Node) -> Result [(DGLinkLab, Node)]
     updateEdge (links@(DGLink gm@(GMorphism cid' lsign lmorphism) _ _),n)
       = if isHomogeneous gm 
            then
             let sourceLid = sourceLogic (Comorphism cid')
             in  {-case fSign sourceLid lsign of
                   Result diagLs (Just lsign') -> 
                       case fMor sourceLid lmorphism of
                         Result diagLm (Just lmorphism') -> -} 
                 case gEmbedComorphism (idComorphism (Logic tlid)) (G_sign tlid lsign) of
                   Result diags1 gmorphism -> 
                       Result diags1 -- (diagLs ++ diagLm) 
                               (Just [(links{dgl_morphism=
                                                   fromJust gmorphism
                                            }, n)])                    

{-
                             case idComorphism (Logic tlid) of 
                                   Comorphism cid2 ->
                                       Result [] -- (diagLs ++ diagLm) 
                                         (Just [(links{dgl_morphism=
                                            GMorphism cid2 lsign lmorphism
                                                      }, n)])
-}            else  Result [mkDiag Hint ("Link is not homogeneous.") ()] (Just [(links,n)])

     transDev newL1 newL2 (_, node, _) =
          case transTh $ dgn_theory node of
               Just th' -> Just (newL1, node {dgn_theory = th'
                                             ,dgn_nf = Nothing
                                             ,dgn_sigma = Nothing}, newL2)
               Nothing  -> Nothing

     fSign sourceID sign =
      case coerceSign sourceID slid "" sign of
        Just sign' -> 
            case map_sign cidMor sign' of
              Result diags maybeSign ->
                  case maybeSign of
                    Just (sign'', _) ->
                        Result diags (Just sign'')
                    Nothing -> Result diags Nothing
        Nothing    -> Result [mkDiag Error ("cannot coerce sign" ++ show sign)
                                     ()] Nothing 

     transTh th = case fTh th of
                    Result _ maybeResult -> maybeResult
     fTh (G_theory lid sign thSens) =
      case coerceSign lid slid "" sign of
        Just sign' -> 
            case coerceThSens lid slid "" thSens of
              Just thSens' -> 
                  case map_theory cidMor (sign', toNamedList thSens') of
                    Result diags maybeTh ->
                      -- show diags
                      case maybeTh of
                        Just (sign'', namedS) -> 
                            Result diags (Just (G_theory tlid sign'' (toThSens namedS)))
                        Nothing ->  Result diags Nothing
              Nothing    -> Result [(mkDiag Error ("cannot coerce sens" ++ show thSens)
                                     ())] Nothing 
        Nothing -> Result [(mkDiag Error ("cannot coerce sign" ++ show sign)
                                     ())] Nothing 

     fMor sourceID mor =
        case coerceMorphism sourceID slid "" mor of
          Just mor' -> 
              map_morphism cidMor mor' 

          Nothing   -> Result [(mkDiag Error ("cannot coerce mor" ++ show mor)
                                ())] Nothing  



