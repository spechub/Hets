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
import CASL.Logic_CASL
import Comorphisms.CASL2PCFOL
import Comorphisms.CASL2SubCFOL

-- translation between two GlobalContext on the basis the given Comorphism 
dg_translation :: GlobalContext -> AnyComorphism -> Result GlobalContext
dg_translation gc cm@(Comorphism cidMor) =
    mainTrans (Map.keys $ toMap $ devGraph gc) [] gc
  where  
        mainTrans [] diagsMain gcon = Result diagsMain (Just gcon)
        mainTrans (h:r) diagsMain gcon =  
            case Map.lookup h (toMap $ devGraph gcon) of
              Just (node@(_, nodeLab, _)) ->
                  if lessSublogicComor 
                         (sublogicOfTh $ dgn_theory nodeLab) cm
                    then let Result diags' maybeGC = updateNode h gcon cm 
                         in  case maybeGC of
                              Just gc' -> mainTrans r (diagsMain ++ diags') gc'
                              Nothing -> mainTrans r (diagsMain ++ diags') gc
                    else  let gcon' = changeThOfNode node  gcon
			      hintDiag = diagsMain ++ [(mkDiag Hint ("node " ++ (show h) ++
					":" ++ (show $ dgn_name nodeLab) ++
					" is not less than " ++ (show cm) ++ 
                                        " -- change the theory...") ())] 
			  in mainTrans r hintDiag gcon'
              Nothing -> mainTrans r (diagsMain ++ [(mkDiag Error ("node " ++ (show h) 
                              ++ " is not found in graph.") ())]) gcon
			      
	     where changeThOfNode (lin, nodeLab, lout) globalContext =
                     case dgn_theory nodeLab of
                      G_theory lid sign0 sens0 ->
		       let th = (sign0, toNamedList sens0)
                           Result _ (Just (sign1, sens1)) = do
						th0 <- coerceBasicTheory lid CASL "" th
						th1 <- wrapMapTheory CASL2PCFOL th0
						wrapMapTheory CASL2SubCFOL th1
		       in globalContext {devGraph =Gr (Map.update (\_ -> Just (lin, nodeLab{dgn_theory = G_theory (targetLogic CASL2SubCFOL) sign1 (toThSens sens1)}, lout)) h (toMap $ devGraph globalContext))}
				


updateNode :: Int -> GlobalContext -> AnyComorphism -> Result GlobalContext
updateNode index gc acm@(Comorphism cidMor) =
    -- sigMap, thMap and morMap can be empty, so the index of node can
    -- not be found in it.
    let (inLinks, node, outLinks) = 
            fromJust $ Map.lookup index $ toMap $ devGraph gc
        -- Result diagsL1 newL1 = foldl (joinResultWith (\ a b -> a ++ b)) 
        --                       (Result [] (Just [])) (map updateEdge inLinks)
        Result diagsL2 newL2 = foldl (joinResultWith (\ a b -> a ++ b)) 
                               (Result [] (Just [])) (map updateEdge outLinks)
        Result thDiag _ = fTh $ dgn_theory node 
    in  Result (thDiag ++ diagsL2)
                (Just (gc {devGraph=Gr (Map.update (transDev inLinks
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
             let sourceLid = sourceLogic cid'
                 targetLid = targetLogic cid'
             in  
                if lessSublogicComor (G_sublogics 
                            sourceLid (sourceSublogic cid')) acm
                    then
                        case fSign sourceLid lsign of
                          Result diagLs (Just lsign') -> 
                              case fMor targetLid lmorphism of
                                Result diagLm (Just lmorphism') -> 
                                    case idComorphism (Logic tlid) of 
                                      Comorphism cid2 ->
                                          Result (diagLs ++ diagLm) 
                                             (Just [(links{dgl_morphism=
                                                   GMorphism cid2 (fromJust $ coerceSign tlid (sourceLogic cid2) "" lsign') (fromJust $ coerceMorphism tlid (targetLogic cid2) "" lmorphism')
                                                  }, n)])
                                Result diagLm Nothing  -> Result (diagLm ++ [mkDiag Error ("morphism of link can not be translated.") ()]) (Just [(links, n)])
                          Result diagLs Nothing  -> Result (diagLs ++ [mkDiag Error ("sign of link can not be translated.") ()]) (Just [(links, n)])
                    else Result [mkDiag Hint ("GMorphism of a Link from node " ++ (show n) ++ " is not less than ." ++ (show cidMor)) ()] (Just [(links,n)])
            else  Result [mkDiag Hint ("Link is not homogeneous.") ()] (Just [(links,n)])

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
              Result diagsOfcs maybeSign ->
                  case maybeSign of
                    Just (sign'', _) ->
                        Result diagsOfcs (Just sign'')
                    Nothing -> Result diagsOfcs Nothing
        Nothing    -> Result [mkDiag Error ("cannot coerce sign" ++ show sign)
                                     ()] Nothing 

     transTh th = case fTh th of
                    Result _ maybeTh -> maybeTh
     fTh (G_theory lid sign thSens) =
      case coerceSign lid slid "" sign of
        Just sign' -> 
            case coerceThSens lid slid "" thSens of
              Just thSens' -> 
                  case map_theory cidMor (sign', toNamedList thSens') of
                    Result diagsOfth maybeTh ->
                      -- show diags
                      case maybeTh of
                        Just (sign'', namedS) -> 
                            Result diagsOfth (Just (G_theory tlid sign'' (toThSens namedS)))
                        Nothing ->  Result diagsOfth Nothing
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



