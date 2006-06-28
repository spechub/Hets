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

-- translation between two GlobalContext on the basis the given Comorphism 
dg_translation :: GlobalContext -> AnyComorphism -> Result GlobalContext
dg_translation gc cm@(Comorphism cidMor) =
    mainTrans (Map.keys $ toMap $ devGraph gc) [] gc
  where  
        mainTrans [] diags gc = Result diags (Just gc)
        mainTrans (h:r) diags gc =  
            case Map.lookup h (toMap $ devGraph gc) of
              Just (_, nodeLab, _) -> 
               if lessSublogicComor (sublogicOfTh $ dgn_theory nodeLab) cm
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
    let Result smDiag _ = case Map.lookup index (sigMap gc) of
                            Just sigElem -> fSign sigElem
                            Nothing -> Result [] Nothing
        Result tmDiag _ = case Map.lookup index (thMap gc) of
                            Just thElem -> fTh thElem
                            Nothing -> Result [] Nothing
        Result mmDiag _ = case Map.lookup index (morMap gc) of
                            Just morElem -> fMor morElem
                            Nothing -> Result [] Nothing
        (l1, node, l2) = 
            fromJust $ Map.lookup index $ toMap $ devGraph gc
        Result thDiag _ = fTh $ dgn_theory node 
        Result morDiag _ = fGMor $ dgn_sigma node
    in  Result (thDiag++morDiag++smDiag++tmDiag++mmDiag)
               (Just (gc {devGraph = Gr (Map.update transDev index 
                                           (toMap $ devGraph gc))
                         , sigMap = Map.update 
                                    transSig 
                                    index (sigMap gc)
                         , thMap = Map.update
                                   transTh 
                                   index (thMap gc)
                         , morMap = Map.update
                                    transMor 
                                    index (morMap gc)
                         }))
   where 
     slid = sourceLogic cidMor
     tlid = targetLogic cidMor
     transSig sign = case fSign sign of
                       Result _ maybeResult -> maybeResult
     fSign (G_sign lid sign) =
      case coerceSign lid slid "" sign of
        Just sign' -> 
            case map_sign cidMor sign' of
              Result diags maybeSign ->
                  case maybeSign of
                    Just (sign'', _) ->
                        Result diags (Just (G_sign tlid sign''))
                    Nothing -> Result diags Nothing
        Nothing    -> Result [(mkDiag Error ("cannot coerce sign" ++ show sign)
                                     ())] Nothing 

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

     transMor mor = case fMor mor of 
                      Result _ maybeResult -> maybeResult
     fMor (G_morphism lid mor) =
        case coerceMorphism lid slid "" mor of
          Just mor' -> 
              case map_morphism cidMor mor' of
                Result diags maybeMor ->
                    Result diags $ maybe Nothing 
                            (Just . G_morphism tlid) maybeMor
          Nothing   -> Result [(mkDiag Error ("cannot coerce mor" ++ show mor)
                                     ())] Nothing  
     -- should cid also translated? and how? 
     fGMor gm@(Just (GMorphism cid sign1 mor2)) =
{-         let (Result diagsS mSign1) = fSign (G_sign (sourceLogic cid) sign1) 
             (Result diagsM mMor2) = fMor (G_morphism (sourceLogic cid) mor2)
         in  case mSign1 of 
               Just sign1' ->
                   case mMor2 of
                     Just mor2' -> Result (diagsS ++ diagsM) 
                                     (Just (GMorphism cid sign1' mor2'))
                     _ -> Result (diagsS ++ diagsM) Nothing
               Nothing -> Result (diagsS ++ diagsM) Nothing
-}
           Result [] gm
     fGMor Nothing = Result [mkDiag Warning ("node " ++ (show index) ++ " no GMorphism") ()] Nothing
         
     transDev (l1, node, l2) =
         case transTh $ dgn_theory node of
           Just th' -> Just (l1, node {dgn_theory = th'}, l2)
           Nothing  -> Nothing


