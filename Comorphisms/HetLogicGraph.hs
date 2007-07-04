{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich and Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  unstable
Portability :  non-portable

Assembles the computation of or the pre-computed het Sublogic Graph.

-}


module Comorphisms.HetLogicGraph (hetSublogicGraph) where

import Comorphisms.LogicGraph

import qualified Common.Lib.Rel as Rel

import Logic.Logic
import Logic.Prover (prover_sublogic)
import Logic.Comorphism
import Logic.Grothendieck
import Logic.Coerce

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (fromJust)
import Data.List


{- |
   initial version of a logic graph based on ticket #336
-}
hetSublogicGraph :: HetSublogicGraph
hetSublogicGraph = removeDuplicateComorphisms $
                   addHomogeneousInclusions $
                   reduceToWellSupported $ 
                   removeLoops $ 
                   hsg_union imageHsg $ 
                   HetSublogicGraph
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
                 , Map.insertWith (++) (show srcGsl, show trgGsl) [acm] emp)

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
              foldl (imageAndPreImageOf gsl) hsg $
                     Map.elems $ comorphisms logicGraph 
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

removeDuplicateComorphisms :: HetSublogicGraph
                           -> HetSublogicGraph
removeDuplicateComorphisms hsg = 
      hsg {comorphismEdges = Map.filter (not . null) $ 
                             Map.map nub $ comorphismEdges hsg }    

hsg_union :: HetSublogicGraph
          -> HetSublogicGraph
          -> HetSublogicGraph
hsg_union hsg1 hsg2 = 
    HetSublogicGraph { sublogicNodes = Map.union (sublogicNodes hsg1)
                                                (sublogicNodes hsg2)
                     , comorphismEdges = 
                         Map.unionWith (++) (comorphismEdges hsg1)
                                            (comorphismEdges hsg2)
                     }

compute_mapSublogic_preImage :: AnyComorphism 
                             -> (AnyComorphism,
                                 Map.Map G_sublogics (Set.Set G_sublogics))
compute_mapSublogic_preImage (Comorphism cid) =
    case onlyMaximal_preImage $ mapSublogic_preImage cid of
      preImageMap -> (Comorphism cid, preImageMap)
    
comorPreImages :: [(AnyComorphism, Map.Map G_sublogics (Set.Set G_sublogics))]
comorPreImages = map compute_mapSublogic_preImage $ comorphismList

lookupPreImage :: AnyComorphism -> G_sublogics -> [G_sublogics]
lookupPreImage acm gsl = 
    case lookup acm comorPreImages of
      Nothing -> error "unknown Comorphism"
      Just preImageMap ->
               maybe [] Set.toList $ 
               Map.lookup gsl preImageMap

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
                   => cid -> Map.Map G_sublogics (Set.Set G_sublogics)
mapSublogic_preImage cid = 
    Map.foldWithKey toG_sublogics Map.empty $
    preImageMaybe (mapSublogic cid) $ all_sublogics $ sourceLogic cid
    where toG_sublogics s2 set_s1 = 
             Map.insert (G_sublogics (targetLogic cid) s2) 
                        (Set.map (G_sublogics (sourceLogic cid)) set_s1)
{- onlyMaximal_preImage :: (Comorphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2)
                   => cid 
                     -> Map.Map sublogics2 (Set.Set sublogics1)
                     -> Map.Map sublogics2 (Set.Set sublogics1)
-}
onlyMaximal_preImage :: Map.Map G_sublogics (Set.Set G_sublogics) 
                     -> Map.Map G_sublogics (Set.Set G_sublogics)
onlyMaximal_preImage preImageMap = Map.map shrink preImageMap
    where shrink st = Set.fromList $ shrink' [] $ Set.elems st
          shrink' acc [] = acc
          shrink' acc (x:xs) = if any (isProperSublogic x) (xs++acc) 
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
        , comorphismEdges = Map.insertWith (++) (show src,show trg) [acm] $
                            comorphismEdges hsg }

removeLoops :: HetSublogicGraph -> HetSublogicGraph
removeLoops hsg = hsg { comorphismEdges = 
                            Map.filterWithKey (\ (s,t) _ -> s/=t) $
                            comorphismEdges hsg}

reduceToWellSupported :: HetSublogicGraph -> HetSublogicGraph
reduceToWellSupported hsg = 
    hsg { sublogicNodes = wellSupN
        , comorphismEdges = wellSupE }
    where wellSupN = Map.filter isWellSupN $ sublogicNodes hsg
          wellSupE = Map.filterWithKey isWellSupE $ comorphismEdges hsg
          isWellSupN (G_sublogics lid _) = 
              (hasProver lid) ||  (case stability lid of
                                     Stable -> True
                                     Testing -> True
                                     _ -> False)
          isWellSupE (s,t) _ = Map.member s wellSupN && Map.member t wellSupN
          hasProver lid = not $ null $ provers lid
                                     
addHomogeneousInclusions :: HetSublogicGraph -> HetSublogicGraph
addHomogeneousInclusions hsg =
    hsg {comorphismEdges = Map.unionWith (++) homogeneousIncls $
                                              comorphismEdges hsg}
    where homogeneousIncls = Map.unionsWith (++) $  
                             map toMap $ Rel.partSet sameLogic $ 
                             Set.fromList $ Map.elems $ sublogicNodes hsg
          sameLogic (G_sublogics lid1 _) (G_sublogics lid2 _) =
              Logic lid1 == Logic lid2 
          toMap s = Map.fromList $ map toIncComor $
                    Rel.toList $ Rel.intransKernel $ Rel.fromList 
                    [ (x,y) | x <- Set.toList s 
                            , y <- Set.toList s
                            , isProperSublogic x y ]
          toIncComor (x@(G_sublogics lid1 sub1)
                     ,y@(G_sublogics lid2 sub2)) = 
                 ( (show x,show y)
                 , [maybe (error $ "addHomogeneousInclusions: "++
                                   "should be an inclusion") 
                         Comorphism $ 
                          mkInclComorphism lid1 sub1 $ 
                             forceCoerceSublogic lid2 lid1 sub2])

