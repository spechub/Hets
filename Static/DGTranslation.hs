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
import qualified List as List (nub)
import Common.Result
import Maybe
import Common.Lib.Graph
import Data.Graph.Inductive.Graph
-- import CASL.Logic_CASL
-- import Common.AS_Annotation
-- import Common.DocUtils
import Control.Exception
import Debug.Trace
-- import Common.Id

-- | translation a GlobalContext on the basis the given Comorphism 
-- | if the sublogic of (theory of) node less than given Comorphism
-- | then call the process to translate;
-- | otherwise do not translate the graph. 
dg_translation :: GlobalContext -> AnyComorphism -> Result GlobalContext
dg_translation gc cm =
    mainTrans (Map.keys $ toMap $ devGraph gc) [] gc
  where  
    -- rekursiv translate alle nodes of DevGraph of GlobalContext
    mainTrans [] diagsMain gcon = Result diagsMain (Just gcon)
    mainTrans (h:r) diagsMain gcon =  
        case Map.lookup h (toMap $ devGraph gcon) of
          Just (_, nodeLab, _) ->
           -- if the sublogic of (theory of) node less than given Comorphism
           -- then call the process to translate;
           -- otherwise do not translate the graph.
           if lessSublogicComor 
                  (sublogicOfTh $ dgn_theory nodeLab)  cm
              then let Result diags' maybeGC = updateNode h gcon cm 
                   in  case maybeGC of
                         Just gc' -> mainTrans r (diagsMain ++ diags') gc'
                         Nothing -> mainTrans r (diagsMain ++ diags') gc
              else  let -- gcon' = changeThOfNode node  gcon
			hintDiag = diagsMain ++ 
                                   [(mkDiag Error ("node " ++ (show h) ++
				     ":" ++ (show $ dgn_name nodeLab) ++
			             " is not less than " ++ (show cm) ++ 
                                     " -- change the theory...") ())] 
              --          Result diags' maybeGC = updateNode h gcon cm 
		    in  -- case maybeGC of
                --          Just gc' -> 
                --             mainTrans r (diagsMain++hintDiag++diags') gc'
                --          Nothing -> 
                             mainTrans r (diagsMain++hintDiag) gc
                     
          Nothing -> mainTrans r (diagsMain ++ 
                                  [(mkDiag Error ("node " ++ (show h) 
                              ++ " is not found in graph.") ())]) gcon

{-
              -- if theory of a node not less than the given comorphism
              -- change the thoery to SubCFOL ...
        where changeThOfNode (lin, nodeLab, lout) globalContext =
                case dgn_theory nodeLab of
                  G_theory lid sign0 sens0 ->
		    let th = (sign0, toNamedList sens0)
                        Result _ (Just (sign1, sens1)) = do
				th0 <- coerceBasicTheory lid CASL "" th
				th1 <- wrapMapTheory CASL2PCFOL th0
				wrapMapTheory CASL2SubCFOL th1
		    in globalContext 
                        {devGraph =
                          Gr (Map.update 
                              (\_ -> Just (lin, nodeLab{ dgn_theory = 
                                         G_theory (targetLogic CASL2SubCFOL) 
                                         sign1 (toThSens sens1)},lout)) 
                              h (toMap $ devGraph globalContext))}
	-}
		
-- | update the translated node	
updateNode :: Int     -- ^ the number of node
		   -> GlobalContext -> AnyComorphism -> Result GlobalContext
updateNode index gc acm@(Comorphism cidMor) =
    let (inLinks, node, outLinks) = 
            fromJust $ Map.lookup index $ toMap $ devGraph gc
        -- wir translate only the links which are end at this node (inLinks)
        -- only the sentences of from-links to be merged in theory of node
        Result diagsL1 (Just (newL1, toMergedSent1)) = 
            foldl (joinResultWith (\ (a, sen1) (b, sen2) -> 
                                       (a ++ b, List.nub (sen1 ++sen2)))) 
                      (Result [] (Just ([], []))) (map (updateEdge True) 
                                                       inLinks)
        Result diagsL2 (Just (newL2, _)) = 
            foldl (joinResultWith (\ (a, sen1) (b, sen2) -> 
                                       (a ++ b, List.nub (sen1 ++sen2)))) 
                      (Result [] (Just ([], []))) (map (updateEdge False) 
                                                       outLinks)
        Result thDiag newNode = transTh newL1 newL2 toMergedSent1 node
   
    in {- if length newL1 /= 0 then -}  
        Result (diagsL1 ++diagsL2 ++ thDiag)
                (Just (gc {devGraph=Gr (Map.update (\_ -> newNode)  
                                        index 
                                        (toMap $ devGraph gc))

                          }))
      --    else  Result (diagsL1 ++ diagsL2 ++ thDiag) (Just gc) 

   where 
     slid = sourceLogic cidMor
     tlid = targetLogic cidMor

     -- update the edges of a node
     -- if the sublogic of (sign and morphism of) node less than given 
     -- Comorphism then translate the GMorphism, otherwise give out a
     -- Error-Diagnosis, but the GMorphism is not translated.
     -- (inlink, node)
     -- updateEdge :: (DGLinkLab, Node) 
     --            -> Result ([(DGLinkLab, Node)], [Named sentence2])]
     updateEdge isDebug (links@(DGLink gm@(GMorphism cid' lsign lmorphism) 
                                       _ _),n)
       = if isHomogeneous gm 
          then
           let sourceLid = sourceLogic cid'
               targetLid = targetLogic cid'
           in if {- lessSublogicComor (G_sublogics 
                             sourceLid (sourceSublogic cid')) acm  -}
                 (lessSublogicComor (sublogicOfSign (G_sign sourceLid lsign))
                                    acm) 
                 && (lessSublogicComor (sublogicOfMor (G_morphism targetLid 
                                                       lmorphism)) acm)
               then
                  -- translate sign of GMorphism
                 case fSign sourceLid lsign of
                   Result diagLs (Just (lsign', lsens)) -> 
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
                                slNewMor  = sublogicOfMor $ 
                                               G_morphism (targetLogic cid2) 
                                                          newMor
                                res = Result (diagLs ++ diagLm ++ 
                                 [mkDiag Hint 
                                    "successful translation of edge." ()])
                                            (Just ([(links{dgl_morphism=
                                                           GMorphism cid2 
                                                           newSign newMor
                                                          }, n)], lsens))
                            in  assert (slNewSign == slNewMor) 
                                    $ if not isDebug then res else res 
                                          {diags = diags res ++ 
                                           [mkDiag Warning ((show $ getNameOfNode n gc) ++ "->" ++ (show $ getNameOfNode index gc) ++ ": " ++ (show $ sublogicOfSign (G_sign sourceLid lsign)) ++ " --> " ++ (show slNewSign)) ()] }
                       Result diagLm Nothing  ->  Result (diagLm ++ 
                         [mkDiag Error 
                          ("morphism of link can not be translated.") ()]) 
                         (Just ([(links, n)], []))
                   Result diagLs Nothing  -> Result (diagLs ++ 
                         [mkDiag Error 
                          ("sign of link can not be translated.") ()]) 
                         (Just ([(links, n)], []))
               else Result [mkDiag Error ("GMorphism of a Link to node " ++ 
                                         (show $ getNameOfNode n gc) ++ 
                                         " is not less than ." ++ 
                                         (show cidMor)) ()] 
                        (Just ([(links,n)], []))
          else Result [mkDiag Error ("Link is not homogeneous.") ()] 
                     (Just ([(links,n)], []))
                  
     -- to translate sign
     fSign sourceID sign =
      case coerceSign sourceID slid "" sign of
        Just sign' -> 
            case map_sign cidMor sign' of
              Result diagsOfcs maybeSign ->
                  case maybeSign of
                    Just (sign'', sens) ->
                        Result (diagsOfcs
                                ++[mkDiag Hint 
                                   "successful translation of sign." ()]) 
                               (Just (sign'',sens))
                    Nothing -> error "Result diagsOfcs Nothing"
        Nothing  -> Result [mkDiag Error ("cannot coerce sign" ++ show sign)
                            ()] Nothing 

     -- to translate theory
     transTh newL1 newL2 toMergedSens node =
         case fTh toMergedSens node $ dgn_theory node of
           Result diagsT maybeTh -> 
               case maybeTh of
                 Just th' -> 
                     Result diagsT (Just (newL1, node {dgn_theory = th'
                                                      ,dgn_nf = Nothing
                                                      ,dgn_sigma = Nothing}, 
                                          newL2))
                 Nothing  -> Result diagsT Nothing

     fTh tmSens _ g@(G_theory lid sign thSens) =
      case coerceSign lid slid "" sign of
        Just sign' -> 
            case coerceThSens lid slid "" thSens of
              Just thSens' -> 
                  case map_theory cidMor (sign', toNamedList thSens') of
                    Result diagsOfth maybeTh ->
                      -- show diags
                      case maybeTh of
                        Just (sign'', namedS) -> 
                            Result (diagsOfth ++ [mkDiag Hint "successful translation of theory" ()]) (Just (let x = G_theory tlid sign'' (toThSens $ List.nub (namedS {- ++ tmSens -} )) in trace ((show $ getNameOfNode index gc) ++ ": " ++ (show $ sublogicOfTh g) ++ " -> " ++ (show $ sublogicOfTh x)) x))
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
                  diagZ = [mkDiag Hint "successful translation of morphism."
                                      ()]
              in  Result (diagsM ++ diagZ) res
          Nothing -> Result [(mkDiag Error ("cannot coerce mor" ++ show mor)
                              ())] Nothing  

getNameOfNode :: Node -> GlobalContext -> NODE_NAME
getNameOfNode index gc =
     let (_, node, _) = fromJust $ Map.lookup index $ toMap $ devGraph $ gc
     in  dgn_name node


