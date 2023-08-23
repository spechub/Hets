{- |
Module      :  ./Comorphisms/HetLogicGraph.hs
Description :  Compute graph with logics and interesting sublogics
Copyright   :  (c) Klaus Luettich and Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  unstable
Portability :  non-portable

Assembles the computation of or the pre-computed het Sublogic Graph.
-}

module Comorphisms.HetLogicGraph
  ( HetSublogicGraph (..)
  , hetSublogicGraph
  , hsg_union
  ) where

import Comorphisms.LogicGraph

import qualified Common.Lib.Rel as Rel
import Common.Utils (keepMins)

import Logic.Logic
import Logic.Prover
import Logic.Comorphism
import Logic.Grothendieck
import Logic.Coerce

import Control.Monad
import qualified Control.Monad.Fail as Fail

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.List

{- | Heterogenous Sublogic Graph
this graph only contains interesting Sublogics plus comorphisms relating
these sublogics; a comorphism might be mentioned multiple times -}
data HetSublogicGraph = HetSublogicGraph
    { sublogicNodes :: Map.Map String G_sublogics
    , comorphismEdges :: Map.Map (String, String) [AnyComorphism]}

emptyHetSublogicGraph :: HetSublogicGraph
emptyHetSublogicGraph = HetSublogicGraph Map.empty Map.empty

toTopSublogicAndProverSupported :: Map.Map String G_sublogics
  -> AnyLogic -> IO (Map.Map String G_sublogics)
toTopSublogicAndProverSupported mp (Logic lid) = do
  ps <- filterM (fmap isNothing . proverUsable) $ provers lid
  cs <- filterM (fmap isNothing . ccUsable) $ cons_checkers lid
  let toGSLPair sl = let gsl = G_sublogics lid sl in (show gsl, gsl)
      top_gsl = toGSLPair $ top_sublogic lid
      prv_sls = map proverSublogic ps ++ map ccSublogic cs
  return . Map.union mp . Map.fromList $ top_gsl : map toGSLPair prv_sls

{- |
   initial version of a logic graph based on ticket #336
-}
hetSublogicGraph :: IO HetSublogicGraph
hetSublogicGraph = do
  let insP = uncurry Map.insert
      toGsl :: Logic
                     lid
                     sublogics
                     basic_spec
                     sentence
                     symb_items
                     symb_map_items
                     sign
                     morphism
                     symbol
                     raw_symbol
                     proof_tree =>
                   lid -> sublogics -> G_sublogics
      toGsl = G_sublogics
      toPair gsl = (show gsl, gsl)
      srcSubl acm nmp = case acm of
             Comorphism cm ->
              let srcSL = sourceSublogic cm
                  srcLid = sourceLogic cm
                  srcGsl = toGsl srcLid srcSL
              in insP (toPair srcGsl) nmp
      initialInterestingSublogics sl = do
        m1 <- foldM toTopSublogicAndProverSupported Map.empty
          . Map.elems $ logics logicGraph
        return . Map.union m1 $ foldr sl Map.empty comorphismList
  is <- initialInterestingSublogics srcSubl
  return . removeDuplicateComorphisms
    . addHomogeneousInclusions
    . reduceToWellSupported
    . removeLoops
    . addComorphismEdges $
                   emptyHetSublogicGraph
                     { sublogicNodes =
                           Map.union is
                                     (compute_preImageOfG_sublogics
                                             is)}


{- | adds the interesting comorphisms without adding new nodes;
considering as start and end points only existing nodes -}
addComorphismEdges :: HetSublogicGraph -> HetSublogicGraph
addComorphismEdges hsg = Map.foldr insComs hsg $ sublogicNodes hsg
    where insComs gsl h = foldr (insCom gsl) h comorphismList
          insCom gsl acm hsg' =
             case acm of
               Comorphism cm ->
                case gsl of
                  G_sublogics g_lid sl ->
                    if language_name (sourceLogic cm) /= language_name g_lid
                    then hsg'
                    else maybe hsg' (addEdge hsg' gsl acm .
                                     G_sublogics (targetLogic cm))
                               (coerceSublogic g_lid (sourceLogic cm) "aCE" sl
                                >>= mapSublogic cm)
          addEdge hsg' srcGsl acm trgGsl =
              foldr (\ x -> fromMaybe (error ("insertion of " ++
                                         show acm ++ " failed!")) .
                           insertEdge srcGsl x acm) hsg' $
                    minimalSuperGsl trgGsl
          minimalSuperGsl gsl =
              if Map.member (show gsl) $ sublogicNodes hsg
              then [gsl]
              else case filter (\ x -> Set.size
                                        (Set.filter (sameLogic gsl) x) > 0) $
                                 partSetSameLogic $ sublogicNodes hsg of
                              [] -> error "no appropiate superlogics"
                              [x] -> keepMins isProperSublogic $
                                     filter (isProperSublogic gsl) $
                                     Set.toList x
                              _ -> error "to many sets"

{- | compute all the pre-images of the list of G_sublogics
under all suitable comorphisms -}
compute_preImageOfG_sublogics :: Map.Map String G_sublogics
             -- ^ initial interesting sublogics
                              -> Map.Map String G_sublogics
compute_preImageOfG_sublogics =
    iterComor Map.empty Map.empty
    where iterComor newSublMap alreadyTried queue
           | Map.null queue = newSublMap
           | otherwise =
               case Map.deleteFindMin queue of
                 ((k, gsl), q') ->
                     case calcPreImage gsl Map.empty of
                       nMap -> let alreadyTried' =
                                       Map.insert k gsl alreadyTried
                                   newInter = foldr Map.delete nMap
                                                    (Map.keys alreadyTried')
                               in iterComor (Map.union nMap newSublMap)
                                            alreadyTried'
                                            (Map.union newInter q')
          calcPreImage gsl sublMap =
              foldl (preImageOf gsl) sublMap comorphismList
          preImageOf gsl sublMap acm =
              case acm of
               Comorphism cm ->
                 case gsl of
                  G_sublogics g_lid _ ->
                     if language_name (sourceLogic cm) /= language_name g_lid
                        then sublMap
                        else foldr (\ preImg -> Map.insert (show preImg)
                                                           preImg )
                                     sublMap (lookupPreImage acm gsl)

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
comorPreImages = map compute_mapSublogic_preImage comorphismList

lookupPreImage :: AnyComorphism -> G_sublogics -> [G_sublogics]
lookupPreImage acm gsl =
    case lookup acm comorPreImages of
      Nothing -> error "unknown Comorphism"
      Just preImageMap -> maybe [] Set.toList $ Map.lookup gsl preImageMap

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
    Map.foldrWithKey toG_sublogics Map.empty $
    preImageMaybe (mapSublogic cid) $ all_sublogics $ sourceLogic cid
    where toG_sublogics s2 set_s1 =
             Map.insert (G_sublogics (targetLogic cid) s2)
                        (Set.map (G_sublogics (sourceLogic cid)) set_s1)

onlyMaximal_preImage :: Map.Map G_sublogics (Set.Set G_sublogics)
                     -> Map.Map G_sublogics (Set.Set G_sublogics)
onlyMaximal_preImage = Map.map shrink
    where shrink st = Set.fromList $ shrink' [] $ Set.elems st
          shrink' acc [] = acc
          shrink' acc (x : xs) = if any (isProperSublogic x) (xs ++ acc)
                               then shrink' acc xs
                               else shrink' (x : acc) xs

{- | inserts an edge into the graph without checking if the
sublogic pair is compatible with the comorphism;
but both nodes must be already present in the graph -}
insertEdge :: (Fail.MonadFail m) =>
              G_sublogics -> G_sublogics
           -> AnyComorphism -> HetSublogicGraph
           -> m HetSublogicGraph
insertEdge src trg acm hsg =
    if Map.member (show src) (sublogicNodes hsg) &&
       Map.member (show src) (sublogicNodes hsg)
    then return $
         hsg { comorphismEdges = Map.insertWith (++)
                                                (show src, show trg) [acm] $
                                                comorphismEdges hsg }
    else Fail.fail ("Comorphisms.HetLogicGraph: insertEdge: both nodes need " ++
               "to be present")

removeLoops :: HetSublogicGraph -> HetSublogicGraph
removeLoops hsg = hsg { comorphismEdges =
                            Map.filterWithKey (\ (s, t) _ -> s /= t) $
                            comorphismEdges hsg}

reduceToWellSupported :: HetSublogicGraph -> HetSublogicGraph
reduceToWellSupported hsg =
    hsg { sublogicNodes = wellSupN
        , comorphismEdges = wellSupE }
    where wellSupN = Map.filter isWellSupN $ sublogicNodes hsg
          wellSupE = Map.filterWithKey isWellSupE $ comorphismEdges hsg
          isWellSupN (G_sublogics lid _) =
              hasProver lid || (case stability lid of
                                     Stable -> True
                                     Testing -> True
                                     _ -> False)
          isWellSupE (s, t) _ = Map.member s wellSupN && Map.member t wellSupN
          hasProver lid = not $ null $ provers lid

sameLogic :: G_sublogics -> G_sublogics -> Bool
sameLogic (G_sublogics lid1 _) (G_sublogics lid2 _) =
    Logic lid1 == Logic lid2

partSetSameLogic :: Map.Map String G_sublogics
                 -> [Set.Set G_sublogics]
partSetSameLogic = Rel.partSet sameLogic . Set.fromList . Map.elems

addHomogeneousInclusions :: HetSublogicGraph -> HetSublogicGraph
addHomogeneousInclusions hsg =
    hsg {comorphismEdges = Map.unionWith (++) homogeneousIncls $
                                              comorphismEdges hsg}
    where homogeneousIncls = Map.unionsWith (++) $
                             map toMap $ partSetSameLogic $ sublogicNodes hsg
          toMap s = Map.fromList $ map toIncComor $
                    Rel.toList $ Rel.intransKernel $ Rel.fromList
                    [ (x, y) | x <- Set.toList s
                            , y <- Set.toList s
                            , isProperSublogic x y ]
          toIncComor (x@(G_sublogics lid1 sub1)
                     , y@(G_sublogics lid2 sub2)) =
                 ( (show x, show y)
                 , [maybe (error $ "addHomogeneousInclusions: " ++
                                   "should be an inclusion")
                         Comorphism $
                          mkInclComorphism lid1 sub1 $
                             forceCoerceSublogic lid2 lid1 sub2])
