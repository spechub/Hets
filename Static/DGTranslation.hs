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


dg_translation :: GlobalContext -> AnyComorphism -> GlobalContext
dg_translation gc cm@(Comorphism cidMor) =
    mainTrans (Map.keys $ thMap gc) gc
  where 
        mainTrans [] gc = gc
        mainTrans (h:r) gc =  
            case Map.lookup h (thMap gc) of
              Just value -> if lessSublogicComor (sublogicOfTh value) cm
                               then mainTrans r $ updateNode h gc cm
                               else mainTrans r gc

updateNode :: Int -> GlobalContext -> AnyComorphism -> GlobalContext
updateNode index gc cm@(Comorphism cidMor) =
    gc { sigMap = Map.update 
                  transSig 
                  index (sigMap gc)
       , thMap = Map.update
                 transTh 
                 index (thMap gc)
       , morMap = Map.update
                  transMor 
                  index (morMap gc)
       }

   where 
     transSig sign = fSign (sourceLogic cidMor) sign
     fSign slid (G_sign lid sign) =
      case coerceSign lid slid "" sign of
        Just sign' -> Just (G_sign slid sign')
        Nothing    -> Nothing

     transTh th = fTh (sourceLogic cidMor) th
     fTh slid (G_theory lid sign thSens) =
      case coerceSign lid slid "" sign of
        Just sign' -> 
            case coerceThSens lid slid "" thSens of
              Just thSens' -> Just (G_theory slid sign' thSens')
              Nothing    -> Nothing
        Nothing -> Nothing

     transMor mor = fMor (sourceLogic cidMor) mor
     fMor slid (G_morphism lid mor) =
        case coerceMorphism lid slid "" mor of
          Just mor' -> 
              case map_morphism cidMor mor' of
                Result diags maybeResult ->
                    maybeResult
          Nothing   -> Nothing    

{-
transMor2 :: (Comorphism cid lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items sign1 morphism symbol1 raw_symbol1 proof_tree1 lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2 sign2 morphism symbol2 raw_symbol2 proof_tree2) => cid -> morphism1 -> Maybe morphism2
transMor2 cmid mor =
    case map_morphism cmid mor of
      Result diags maybeResult -> maybeResult

transTh2 :: AnyComorphism  -> Map.Map Int G_theory -> Map.Map Int G_theory
transTh2 (Comorphism cmid) gtMap =
    transTh2' (Map.keys gtMap) gtMap Map.empty
    where 
      transTh2' [] _ resGm = resGm
      transTh2' (h:r) gm newMap =
          case Map.lookup h gm of
            Just (G_theory lid sign thSens) ->
                case map_theory cmid (sign, toNamedList thSens) of
                  Result diags maybeTh ->
                      -- show diags
                      case maybeTh of
                        Just (sign', namedS) -> 
                            transTh2' r gm (Map.insert h 
                              (G_theory lid sign' (toThSens namedS)) newMap)
                        Nothing -> transTh2' r gm newMap
            Nothing -> transTh2' r gm newMap

transSign2 :: AnyComorphism -> Map.Map Int G_sign -> Map.Map Int G_sign
transSign2 (Comorphism cmid) gsMap =
    transSign2' (Map.keys gsMap) gsMap Map.empty
    where
      transSign2' [] _ resGm = resGm
      transSign2' (h:r) gm newMap = 
          case Map.lookup h gm  of
            Just (G_sign lib sign) ->
                case map_sign cmid sign of
                  Result diags maybeSign ->
                      -- show diags
                      case maybeSign of
                        Just (sign', _) -> 
                            transSign2' r gm (Map.insert h 
                                              (G_sign lib sign') newMap)
                        Nothing -> transSign2' r gm newMap
            Nothing -> transSign2' r gm newMap
-}