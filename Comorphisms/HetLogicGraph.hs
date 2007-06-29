{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich and Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  unstable
Portability :  non-portable

Assembles the computation of or the pre-computed het Sublogic Graph.

-}


module Comorphisms.HetLogicGraph ( hetSublogicGraph) where

import Comorphisms.LogicGraph
import Common.Result
import Logic.Logic
import Logic.Prover (prover_sublogic)
import Logic.Comorphism
import Logic.Grothendieck
import Logic.Coerce
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (fromJust,catMaybes)
import Data.List
import Debug.Trace

import Comorphisms.CASL2HasCASL
import Comorphisms.CASL2SubCFOL

import HasCASL.Logic_HasCASL
import CASL.Logic_CASL


{- |
   initial version of a logic graph based on ticket #336
-}
hetSublogicGraph :: HetSublogicGraph
hetSublogicGraph = hsg_union imageHsg $ HetSublogicGraph
    { sublogicNodes = initialInterestingSublogics
    , comorphismEdges = topComorphisms}
    where initialInterestingSublogics = Map.union
             (Map.fold toTopSublogicAndProverSupported Map.empty $ 
                 logics logicGraph) 
               comorphismSrcAndTrgSublogics
          (comorphismSrcAndTrgSublogics,topComorphisms) =
              Map.fold srcAndTrg (Map.empty,Map.empty) $ 
              comorphisms logicGraph
          imageHsg = imageAndPreImage initialInterestingSublogics 
             --  HetSublogicGraph Map.empty Map.empty
          toTopSublogicAndProverSupported al mp = 
              case al of
                Logic lid -> 
                    let toGSLPair sl = let gsl = G_sublogics lid sl
                                       in (show gsl,gsl)
                        top_gsl = toGSLPair $ top_sublogic lid
                        getPrvSL = map prover_sublogic
                        prv_sls = getPrvSL (provers lid) ++
                                  getPrvSL (cons_checkers lid)
                    in Map.union mp $ 
                       Map.fromList (top_gsl :
                                     map toGSLPair prv_sls)

          insP = uncurry Map.insert 
          toGsl lid sl = G_sublogics lid sl
          toPair gsl = (show gsl,gsl)

          srcAndTrg acm (nmp,emp) = 
            case acm of 
             Comorphism cm ->
              let srcSL = sourceSublogic cm
                  srcLid = sourceLogic cm
                  srcGsl = toGsl srcLid srcSL

                  trgSL = targetSublogic cm
                  trgLid = targetLogic cm
                  trgGsl = toGsl trgLid trgSL
              in ( insP (toPair srcGsl) $ insP (toPair trgGsl) nmp
                 , Map.insert (show srcGsl, show trgGsl) acm emp)

-- | compute all the images and pre-images of a G_sublogics 
-- under all suitable comorphisms
imageAndPreImage :: Map.Map String G_sublogics 
                    -- ^ initial interesting sublogics
                 -> HetSublogicGraph
imageAndPreImage initialInterSubl = 
    iterComor emptyHetSublogicGraph Map.empty initialInterSubl
    where iterComor hsg alreadyTried queue 
           | Map.null queue = hsg
           | otherwise = 
               case Map.deleteFindMin queue of
                 ((k,gsl),q') -> 
                     case calcImageAndPreImage gsl emptyHetSublogicGraph of
                       nhsg -> let alreadyTried' = 
                                       (Map.insert k gsl alreadyTried)
                                   newInter = foldr Map.delete 
                                                    (sublogicNodes nhsg)
                                                    (Map.keys alreadyTried')
                               in iterComor (hsg_union nhsg hsg)
                                            alreadyTried'
                                            (Map.union newInter q')
          calcImageAndPreImage gsl hsg = 
              foldl (imageAndPreImageOf gsl) hsg 
                    (delete (Comorphism CASL2HasCASL) $ 
                     Map.elems $ comorphisms logicGraph) 
          imageAndPreImageOf gsl hsg' acm =
              case acm of
               Comorphism cm ->
                 case gsl of
                  G_sublogics g_lid sl ->
                     if language_name (sourceLogic cm) /= language_name g_lid 
                        then hsg'
                        else hsg_union
                              (maybe hsg' -- image
                                 (\ sl' -> insertEdge gsl 
                                             (G_sublogics (targetLogic cm) sl')
                                             acm
                                             hsg' )
                                 (coerceSublogic g_lid (sourceLogic cm) "" sl
                                  >>= mapSublogic cm))
                              (foldr (\preImg -> insertEdge preImg gsl acm) 
                                     emptyHetSublogicGraph 
                                     (lookupPreImage acm gsl))

hsg_union :: HetSublogicGraph
          -> HetSublogicGraph
          -> HetSublogicGraph
hsg_union hsg1 hsg2 = 
    HetSublogicGraph { sublogicNodes = Map.union (sublogicNodes hsg1)
                                                (sublogicNodes hsg2)
                     , comorphismEdges = Map.union (comorphismEdges hsg1)
                                                  (comorphismEdges hsg2)
                     }

test1 :: Comorphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
         => cid -> [[G_sublogics]]
test1 = (\ (cid) -> (\ (m1,_,m) -> 
                 map (map (\e -> G_sublogics (sourceLogic cid) 
                            (Map.findWithDefault (error "") e m1))) $ 
                 map Set.elems $ Map.elems m) $ 
         onlyMaximal_preImage cid $ mapSublogic_preImage cid)

compute_mapSublogic_preImage :: AnyComorphism 
                             -> (AnyComorphism,
                                 ( Map.Map String G_sublogics, -- srcLogic
                                   Map.Map String G_sublogics, -- trgLogic
                                   Map.Map String (Set.Set String)))
                                        -- trg             src
compute_mapSublogic_preImage (Comorphism cid) =
    case -- reduceTables cid $ 
         onlyMaximal_preImage cid $ 
         mapSublogic_preImage cid of
      (mp1,mp2,preImageMap) -> trace (language_name cid++": "++ 
                                      show (head $ Map.keys mp1,Map.size mp2))
          (Comorphism cid,
           (Map.fold (toGl (sourceLogic cid)) Map.empty mp1,
            Map.fold (toGl (targetLogic cid)) Map.empty mp2,
            Map.foldWithKey (toGlStr mp1 mp2) Map.empty  preImageMap))
    where toGl lid v = 
              let gsl = G_sublogics lid v 
              in Map.insert (show gsl) gsl  
          toGlStr mp1 mp2 k v = 
              Map.insert (gslStr (targetLogic cid) mp2 k)
                         (Set.map (gslStr (sourceLogic cid) mp1) v)
          gslStr lid mp x = show $ G_sublogics lid
                            (Map.findWithDefault (error ("not found: "++
                                                         language_name cid++
                                                         "; "++ 
                                                         language_name lid ++
                                                         "; " ++ 
                                                         show (Map.size mp) ++
                                                         "; " ++
                                                         show (head $ 
                                                               Map.keys mp)++
                                                         "; " ++ show x ++
                                                         "\n" ++ 
                                                         show (elem x $
                                                               map show $
                                                               all_sublogics 
                                                               lid))) 
                                                 x mp)

size3 :: (AnyComorphism,
          ( Map.Map String G_sublogics, -- srcLogic
            Map.Map String G_sublogics, -- trgLogic
            Map.Map String (Set.Set String))) 
      -> String
size3 = (\ (c,(x,y,z)) -> show c ++ ": "++ 
           show (Map.size x,Map.size y, Map.size z) ++ "\n")

comorPreImages :: [(AnyComorphism,
                    ( Map.Map String G_sublogics, -- srcLogic
                      Map.Map String G_sublogics, -- trgLogic
                      Map.Map String (Set.Set String)))
                           -- trg             src
                  ]
comorPreImages = map compute_mapSublogic_preImage $ tail comorphismList

lookupPreImage :: AnyComorphism -> G_sublogics -> [G_sublogics]
lookupPreImage acm gsl = 
    case lookup acm comorPreImages of
      Nothing -> error "unknown Comorphism"
      Just (mp1,mp2,preImageMap) ->
               maybe [] 
                     (map (\x -> Map.findWithDefault (error "") x mp1)
                               . Set.elems)
                     (Map.lookup (show gsl) preImageMap)

-- | pre-image of a function relative to the list values
preImage :: (Ord a, Ord b) => (a -> b) -> [a] -> Map.Map b (Set.Set a)
preImage func = foldl ins Map.empty
    where ins mp v = Map.insertWith Set.union (func v) (Set.singleton v) mp

preImageMaybe :: (Ord a, Ord b) => 
                 (a -> Maybe b) -> [a] 
              -> Map.Map b (Set.Set a)
preImageMaybe f vs = 
    (Map.mapKeysMonotonic fromJust . Map.delete Nothing) $ preImage f vs

mapSublogic_preImage :: (Comorphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2)
                   => cid 
                     -> (Map.Map String sublogics1, 
                         Map.Map String sublogics2, 
                         Map.Map String (Set.Set String))
mapSublogic_preImage cid = 
    let insName mp sl = Map.insert (show sl) sl mp
        mp_subl1 = foldl insName Map.empty $ all_sublogics $ sourceLogic cid
        mp_subl2 = foldl insName Map.empty $ all_sublogics $ targetLogic cid
        mapSubl subl1Str = 
            maybe Nothing (Just . show) $ 
            mapSublogic cid $ 
            Map.findWithDefault (error "never ever happens") subl1Str mp_subl1
    in (mp_subl1,mp_subl2,preImageMaybe mapSubl (Map.keys mp_subl1)) 

onlyMaximal_preImage :: (Comorphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2)
                   => cid 
                     -> (Map.Map String sublogics1, 
                         Map.Map String sublogics2, 
                         Map.Map String (Set.Set String))
                     -> (Map.Map String sublogics1, 
                         Map.Map String sublogics2, 
                         Map.Map String (Set.Set String))
onlyMaximal_preImage cid (mp_subl1,mp_subl2,preImageMap) =
    (mp_subl1,mp_subl2,Map.map shrink preImageMap)
    where shrink st = Set.fromList $ map show $ shrink' [] $ 
                      map (\e -> Map.findWithDefault (error "never happens") 
                                 e mp_subl1) $ Set.elems st
          shrink' acc [] = acc
          shrink' acc (x:xs) = if any (isSubElem x) (xs++acc) 
                               then shrink' acc xs 
                               else shrink' (x:acc) xs

-- | inserts an edge into the graph without checking if the 
--   sublogic pair is compatible with the comorphism
insertEdge :: G_sublogics -> G_sublogics 
           -> AnyComorphism -> HetSublogicGraph
           -> HetSublogicGraph
insertEdge src trg acm hsg =
    hsg { sublogicNodes = Map.insert (show trg) trg $ 
                          Map.insert (show src) src $ sublogicNodes hsg
        , comorphismEdges = Map.insert (show src,show trg) acm $
                            comorphismEdges hsg }

size :: HetSublogicGraph -> (Int,Int)
size hsg = (Map.size $ sublogicNodes hsg, Map.size $ comorphismEdges hsg)

test2 :: (Comorphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2)
                   => cid -> Bool
test2 cid = and $
        map (`elem` all_sublogics (targetLogic cid)) $ catMaybes $
        map (mapSublogic cid) (all_sublogics $ sourceLogic cid)

test3 :: Bool
test3 = test2 CASL2HasCASL

test4 :: Bool
test4 = test2 CASL2SubCFOL

