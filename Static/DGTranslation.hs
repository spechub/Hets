{- |
Module      :  $Header$
Copyright   :  Heng Jiang, Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Central data structure for development graphs.
   Follows Sect. IV:4.2 of the CASL Reference Manual.
-}

module Static.DGTranslation where

import Logic.Logic
import Logic.Coerce
import Logic.Comorphism
import Logic.Grothendieck
import Logic.Prover

import Static.DevGraph
import qualified Common.Lib.Map as Map
import Common.Result

translation :: (Comorphism cid lid1 sublogics1 basic_spec1 sentence1 
                symb_items1 symb_map_items1 sign1 morphism1 symbol1 
                raw_symbol1 proof_tree1 lid2 sublogics2 basic_spec2 
                sentence2 symb_items2 symb_map_items2 sign2 morphism2 
                symbol2 raw_symbol2 proof_tree2Comorphism) => 
               GlobalContext -> cid -> GlobalContext
translation gc cidMor =
    let slid = sourceLogic cidMor
        tlid = targetLogic cidMor
    in  gc { sigMap = transSig slid (sigMap gc) 
                  , thMap  = transTh  slid (thMap gc)
                  , morMap = transMor slid (morMap gc)
                  }
{-
    in  gc' { morMap = transMor2 cidMor (morMap gc')
            , thMap = transTh2 cidMor (thMap gc')
            , sigMap = transSign2 cidMor (sigMap gc')
            }

-}
transSig :: (Logic lid sublogics basic_spec sentence symb_items
                 symb_map_items sign1 morphism symbol
                 raw_symbol proof_tree) => 
            lid -> Map.Map Int G_sign -> Map.Map Int G_sign
transSig slid gSignMap1 =
    transSig' (Map.keys gSignMap1) gSignMap1  Map.empty
  where
    transSig' [] _ resMap = resMap
    transSig' (h:r) gSignMap newMap =
        case Map.lookup h gSignMap of
          Just v ->
              case fSign slid v of 
                Just cValue -> 
                    transSig' r gSignMap (Map.insert h cValue newMap)
                Nothing -> transSig' r gSignMap newMap
          Nothing -> transSig' r gSignMap newMap
    
    fSign :: (Logic lid1 sublogics basic_spec sentence symb_items
                 symb_map_items sign1 morphism symbol
                 raw_symbol proof_tree) => 
         lid1 -> G_sign -> Maybe G_sign
    fSign slid' (G_sign lid sign) =
      case coerceSign lid slid' "" sign of
        Just sign' -> Just (G_sign slid' sign')
        Nothing    -> Nothing
        
transTh :: (Logic lid sublogics basic_spec sentence symb_items
                 symb_map_items sign1 morphism symbol
                 raw_symbol proof_tree) =>
           lid -> Map.Map Int G_theory -> Map.Map Int G_theory
transTh slid gThMap1 =
    transTh' (Map.keys gThMap1) gThMap1 Map.empty
  where
    transTh' [] _ resMap = resMap
    transTh' (h:r) gThMap newMap =
        case Map.lookup h gThMap of
          Just v -> 
              case fTh slid v of
                Just cValue -> 
                    transTh' r gThMap (Map.insert h cValue newMap) 
                Nothing     -> transTh' r gThMap newMap
          Nothing -> transTh' r gThMap newMap
    
    fTh :: (Logic lid1 sublogics basic_spec sentence symb_items
                 symb_map_items sign1 morphism symbol
                 raw_symbol proof_tree) =>
         lid1 -> G_theory -> Maybe G_theory
    fTh slid' (G_theory lid sign thSens) =
      case coerceSign lid slid' "" sign of
        Just sign' -> 
            case coerceThSens lid slid' "" thSens of
              Just thSens' -> Just (G_theory slid' sign' thSens')
              Nothing    -> Nothing
        Nothing -> Nothing
                

transMor :: (Logic lid sublogics basic_spec sentence symb_items
                 symb_map_items sign1 morphism symbol
                 raw_symbol proof_tree) =>
            lid -> Map.Map Int G_morphism -> Map.Map Int G_morphism
transMor slid gMorMap1 =
    transMor' (Map.keys gMorMap1) gMorMap1 Map.empty
    where  
      transMor' [] _ resMap = resMap
      transMor' (h:r) gMorMap newMap =
          case Map.lookup h gMorMap of
              Just v -> 
                  case fMor slid v of 
                    Just cValue ->
                        transMor' r gMorMap (Map.insert h cValue newMap)
                    Nothing -> transMor' r gMorMap newMap
              Nothing   -> transMor' r gMorMap newMap

      fMor :: (Logic lid1 sublogics basic_spec sentence symb_items
                 symb_map_items sign1 morphism symbol
                 raw_symbol proof_tree) =>
           lid1 -> G_morphism -> Maybe G_morphism
      fMor slid' (G_morphism lid mor) =
        case coerceMorphism lid slid' "" mor of
          Just mor' -> Just (G_morphism slid' mor')
          Nothing   -> Nothing
        
{-
transMor2 :: (Comorphism cid
                         lid1
                         sublogics1
                         basic_spec1
                         sentence1
                         symb_items1
                         symb_map_items1
                         sign1
                         G_morphism
                         symbol1
                         raw_symbol1
                         proof_tree1
                         lid2
                         sublogics2
                         basic_spec2
                         sentence2
                         symb_items2
                         symb_map_items2
                         sign2
                         G_morphism
                         symbol2
                         raw_symbol2
                         proof_tree2)
             => cid -> Map.Map Int G_morphism -> Map.Map Int G_morphism
transMor2 cmid gMMap =
    transMor2' (Map.keys gMMap) gMMap Map.empty
    where 
      transMor2' [] _ resGm = resGm
      transMor2' (h:r) gm newMap =
          case Map.lookup h gm of
            Just m -> case map_morphism cmid m of
                        Result diags maybeResult -> 
                            -- show diags
                            case maybeResult of
                              Just m' -> 
                                 transMor2' r gm (Map.insert h m' newMap)
                              Nothing -> transMor2' r gm newMap
            Nothing -> transMor2' r gm newMap

transTh2 :: (Comorphism cid
                        lid1
                        sublogics1
                        basic_spec1
                        sentence
                        symb_items1
                        symb_map_items1
                        sign
                        morphism1
                        symbol1
                        raw_symbol1
                        proof_tree1
                        lid2
                        sublogics2
                        basic_spec2
                        sentence
                        symb_items2
                        symb_map_items2
                        sign
                        morphism2
                        symbol2
                        raw_symbol2
                        proof_tree2)
            => 
             cid -> Map.Map Int G_theory -> Map.Map Int G_theory
transTh2 cmid gtMap =
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

transSign2 :: (Comorphism cid
                          lid1
                          sublogics1
                          basic_spec1
                          sentence1
                          symb_items1
                          symb_map_items1
                          sign
                          morphism1
                          symbol1
                          raw_symbol1
                          proof_tree1
                          lid2
                          sublogics2
                          basic_spec2
                          sentence2
                          symb_items2
                          symb_map_items2
                          sign
                          morphism2
                          symbol2
                          raw_symbol2
                          proof_tree2)
              => 
              cid -> Map.Map Int G_sign -> Map.Map Int G_sign
transSign2 cmid gsMap =
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