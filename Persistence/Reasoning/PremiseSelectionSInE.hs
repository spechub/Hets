{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Persistence.Reasoning.PremiseSelectionSInE ( G_SInEResult (..)
                                                  , SInEParameters (..)
                                                  , perform
                                                  , saveToDatabase
                                                  ) where

import PGIP.ReasoningParameters as ReasoningParameters

import Persistence.Database
import Persistence.Schema as DatabaseSchema
import Persistence.Utils

import Common.AS_Annotation
import Common.ExtSign
import Common.LibName
import qualified Common.OrderedMap as OMap
import Common.Timing (measureWallTime, timeOfDayToSeconds)
import Driver.Options
import Logic.Grothendieck
import Logic.Coerce
import Logic.Logic as Logic
import Logic.Prover (toNamed)
import Static.DevGraph
import Static.GTheory

import Control.Monad.IO.Class (MonadIO (..))
import Data.List as List hiding (insert)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable
import Data.Time.LocalTime
import Data.Time.Clock
import Database.Persist hiding ((==.))
import Database.Persist.Sql hiding ((==.))
import Database.Esqueleto hiding (insertBy)

data G_SInEResult =
  forall lid sublogics
    basic_spec sentence symb_items symb_map_items
    sign morphism symbol raw_symbol proof_tree .
  Logic.Logic lid sublogics
    basic_spec sentence symb_items symb_map_items
    sign morphism symbol raw_symbol proof_tree =>
  G_SInEResult { gSineLogic :: lid
               , parameters :: SInEParameters
               , symbolCommonnesses :: Map symbol Int
               , premiseTriggers :: Map symbol [(Double, Named sentence)] -- this list is ordered by the Double
               , leastCommonSymbols :: Map (Named sentence) (symbol, Int)
               , selectedPremises :: Set (Named sentence)
               , selectedPremiseNames :: Set String
               } deriving Typeable

data SInEParameters = SInEParameters { depthLimit :: Maybe Int
                                     , tolerance :: Maybe Double
                                     , premiseNumberLimit :: Maybe Int
                                     } deriving Typeable

perform :: HetcatsOpts
        -> LibEnv
        -> LibName
        -> DGraph
        -> (Int, DGNodeLab)
        -> G_theory
        -> G_sublogics
        -> ReasoningParameters.PremiseSelection
        -> String
        -> IO (Maybe [String], Int, G_SInEResult)
perform opts libEnv libName dGraph nodeLabel
  gTheory@G_theory{gTheoryLogic = gTheoryLid, gTheorySign = extSign}
  gSublogics premiseSelectionParameters goalName = do
  let parameters_ = SInEParameters
        { depthLimit = ReasoningParameters.sineDepthLimit premiseSelectionParameters
        , tolerance = ReasoningParameters.sineTolerance premiseSelectionParameters
        , premiseNumberLimit = ReasoningParameters.sinePremiseNumberLimit premiseSelectionParameters
        }
  let sineResult0 = G_SInEResult
        { gSineLogic = gTheoryLid
        , parameters = parameters_
        , symbolCommonnesses = Map.empty
        , premiseTriggers = Map.empty
        , leastCommonSymbols = Map.empty
        , selectedPremises = Set.empty
        , selectedPremiseNames = Set.empty
        }
  ((premisesM, sineResult), wallTimeOfDay) <- measureWallTime $ do
    let (sineResult1, goal) =
          preprocess opts libEnv libName dGraph nodeLabel gTheoryLid
            gTheory gSublogics sineResult0 goalName
    let sineResult2 =
          selectPremises opts libEnv libName dGraph nodeLabel gTheoryLid extSign gSublogics
            sineResult1 goal
    let premisesM = case sineResult2 of
          G_SInEResult { selectedPremises = premises } ->
            Just $ Set.toList $ Set.map senAttr premises
    return (premisesM, sineResult2)
  return ( premisesM
         , timeOfDayToSeconds wallTimeOfDay
         , sineResult
         )

preprocess :: Logic.Logic lid sublogics basic_spec sentence symb_items
              symb_map_items sign morphism symbol
              raw_symbol proof_tree
           => HetcatsOpts
           -> LibEnv
           -> LibName
           -> DGraph
           -> (Int, DGNodeLab)
           -> lid
           -> G_theory
           -> G_sublogics
           -> G_SInEResult
           -> String
           -> (G_SInEResult, Named sentence)
preprocess opts libEnv libName dGraph nodeLabel sentenceLid G_theory { gTheoryLogic = gTheoryLid, gTheorySens = sentences, gTheorySign = sign } gSublogics sineResult0 goalName =
  let namedSentences = map (uncurry toNamed) $ OMap.toList sentences
      goal' = fromJust $ find ((goalName ==) . senAttr) namedSentences
      goal = coerceSen "preprocess" gTheoryLid sentenceLid goal'
      sineResult1 = computeSymbolCommonnesses gTheoryLid sign sineResult0 namedSentences
      sineResult2 = computeLeastCommonSymbols gTheoryLid sign sineResult1 namedSentences
      sineResult3 = computePremiseTriggers gTheoryLid sign sineResult1 namedSentences
  in  (sineResult3, goal)

computeSymbolCommonnesses :: Logic.Logic lid sublogics basic_spec sentence
                                         symb_items symb_map_items sign
                                         morphism symbol raw_symbol proof_tree
                          => lid
                          -> ExtSign sign symbol
                          -> G_SInEResult
                          -> [Named sentence]
                          -> G_SInEResult
computeSymbolCommonnesses gTheoryLid ExtSign{plainSign = sign}
  sineResult0@G_SInEResult{..} namedSentences =
    let result =
          foldr (\ namedSentence symbolCommonnessesAcc ->
                  foldr (\ symbol symbolCommonnessesAcc' ->
                          Map.insertWith (+) symbol 1 symbolCommonnessesAcc'
                        )
                        symbolCommonnessesAcc $
                        nub $ symsOfSen gTheoryLid sign $ sentence namedSentence
                )
                (coerceSymbolCommonnesses "computeSymbolCommonnesses 1" gSineLogic gTheoryLid symbolCommonnesses)
                namedSentences
    in  withSymbolCommonnesses gTheoryLid result sineResult0
  where
    withSymbolCommonnesses :: Logic.Logic lid sublogics basic_spec sentence
                                          symb_items symb_map_items sign
                                          morphism symbol raw_symbol proof_tree
                           => lid
                           -> Map symbol Int
                           -> G_SInEResult
                           -> G_SInEResult
    withSymbolCommonnesses lid symbolCommonnesses' G_SInEResult{..} =
      G_SInEResult gSineLogic parameters
        (coerceSymbolCommonnesses "withSymbolCommonnesses" lid gSineLogic symbolCommonnesses')
        premiseTriggers leastCommonSymbols selectedPremises selectedPremiseNames

computeLeastCommonSymbols :: Logic.Logic lid sublogics basic_spec sentence
                                         symb_items symb_map_items sign
                                         morphism symbol raw_symbol proof_tree
                          => lid
                          -> ExtSign sign symbol
                          -> G_SInEResult
                          -> [Named sentence]
                          -> G_SInEResult
computeLeastCommonSymbols gTheoryLid ExtSign{plainSign = sign}
  sineResult0@G_SInEResult{..} namedSentences =
  let symbolCommonnesses' =
        coerceSymbolCommonnesses "computeLeastCommonSymbols 1" gSineLogic gTheoryLid symbolCommonnesses
      leastCommonSymbols' =
        coerceLeastCommonSymbols "computeLeastCommonSymbols 2" gSineLogic gTheoryLid leastCommonSymbols
      result =
        foldr (\ namedSentence leastCommonSymbolsAcc ->
                foldr (\ symbol leastCommonSymbolsAcc' ->
                        let commonness =
                              fromJust $ Map.lookup symbol symbolCommonnesses'
                        in  Map.insertWith (\ new (oldSymbol, oldCommonness) ->
                                             if commonness < oldCommonness
                                             then new
                                             else (oldSymbol, oldCommonness)
                                           )
                                           namedSentence
                                           (symbol, commonness)
                                           leastCommonSymbolsAcc'
                      )
                      leastCommonSymbolsAcc $
                      nub $ symsOfSen gTheoryLid sign $ sentence namedSentence
              ) leastCommonSymbols' namedSentences
  in  withLeastCommonSymbols gTheoryLid result sineResult0
  where
    withLeastCommonSymbols :: Logic.Logic lid sublogics basic_spec sentence symb_items
                                          symb_map_items sign morphism symbol
                                          raw_symbol proof_tree
                           => lid
                           -> Map (Named sentence) (symbol, Int)
                           -> G_SInEResult
                           -> G_SInEResult
    withLeastCommonSymbols lid leastCommonSymbols' G_SInEResult{..} =
      G_SInEResult gSineLogic parameters symbolCommonnesses premiseTriggers
        (coerceLeastCommonSymbols "withLeastCommonSymbols" lid gSineLogic leastCommonSymbols')
        selectedPremises selectedPremiseNames

computePremiseTriggers :: Logic.Logic lid sublogics basic_spec sentence symb_items
                                      symb_map_items sign morphism symbol
                                      raw_symbol proof_tree
                       => lid
                       -> ExtSign sign symbol
                       -> G_SInEResult
                       -> [Named sentence]
                       -> G_SInEResult
computePremiseTriggers gTheoryLid ExtSign{plainSign = sign}
  sineResult0@G_SInEResult{..} namedSentences =
  let symbolCommonnesses' =
        coerceSymbolCommonnesses "computePremiseTriggers 1" gSineLogic gTheoryLid symbolCommonnesses
      leastCommonnesses' = coerceLeastCommonSymbols "computePremiseTriggers 2" gSineLogic gTheoryLid leastCommonSymbols
      premiseTriggers' =
        coercePremiseTriggers "computePremiseTriggers 3" gSineLogic gTheoryLid premiseTriggers
      result =
        foldr (\ namedSentence premiseTriggersAcc ->
                let (_,leastCommonness) = fromJust $
                      Map.lookup namedSentence leastCommonnesses'
                in  foldr (\ symbol premiseTriggersAcc' ->
                            let symbolCommonness :: Int
                                symbolCommonness = fromJust $
                                  Map.lookup symbol symbolCommonnesses'
                                minimalTolerance =
                                  ((fromIntegral symbolCommonness /
                                    fromIntegral leastCommonness) :: Double)
                            in  Map.insertWith
                                  (\ _ triggers ->
                                    List.insertBy
                                      (\ (a, _) (b, _) -> compare a b)
                                      (minimalTolerance, namedSentence)
                                      triggers
                                  )
                                  symbol
                                  [(minimalTolerance, namedSentence)]
                                  premiseTriggersAcc'
                          )
                          premiseTriggersAcc $
                          nub $ symsOfSen gTheoryLid sign $ sentence namedSentence
              ) premiseTriggers' namedSentences
  in  withPremiseTriggers gTheoryLid result sineResult0
  where
    withPremiseTriggers :: Logic.Logic lid sublogics basic_spec sentence
                                       symb_items symb_map_items sign morphism
                                       symbol raw_symbol proof_tree
                        => lid
                        -> Map symbol [(Double, Named sentence)]
                        -> G_SInEResult
                        -> G_SInEResult
    withPremiseTriggers lid premiseTriggers' G_SInEResult{..} =
      G_SInEResult gSineLogic parameters symbolCommonnesses
        (coercePremiseTriggers "withPremiseTriggers" lid gSineLogic premiseTriggers')
        leastCommonSymbols selectedPremises selectedPremiseNames


selectPremises :: Logic.Logic lid sublogics basic_spec sentence
                              symb_items symb_map_items sign morphism
                              symbol raw_symbol proof_tree
               => HetcatsOpts
               -> LibEnv
               -> LibName
               -> DGraph
               -> (Int, DGNodeLab)
               -> lid
               -> ExtSign sign symbol
               -> G_sublogics
               -> G_SInEResult
               -> Named sentence
               -> G_SInEResult
selectPremises opts libEnv libName dGraph nodeLabel gTheoryLid
  extSign gSublogics sineResult0@G_SInEResult{..} goal =
  let premiseLimitM = premiseNumberLimit parameters
      depthLimitM = depthLimit parameters
      tolerance_ = fromMaybe 1.0 $ tolerance parameters
  in  selectPremises' opts tolerance_ depthLimitM premiseLimitM 0 gTheoryLid
        extSign sineResult0 [goal]


selectPremises' :: Logic.Logic lid sublogics basic_spec sentence symb_items
                               symb_map_items sign morphism symbol
                               raw_symbol proof_tree
                => HetcatsOpts
                -> Double
                -> Maybe Int
                -> Maybe Int
                -> Int
                -> lid
                -> ExtSign sign symbol
                -> G_SInEResult
                -> [Named sentence]
                -> G_SInEResult
selectPremises' opts tolerance_ depthLimitM premiseLimitM currentDepth
  gTheoryLid extSign@ExtSign{plainSign = sign}
  sineResult@G_SInEResult {..} previouslySelectedNamedSentences
  | isJust depthLimitM && currentDepth >= fromJust depthLimitM = sineResult
  | isJust premiseLimitM && Set.size selectedPremises >= fromJust premiseLimitM = sineResult
  | otherwise =
    foldr (\ previouslySelectedNamedSentence sineResultAcc ->
              foldr (\ symbol sineResultAcc' ->
                      let possiblyTriggeredSentences =
                            fromJust $ Map.lookup symbol premiseTriggers'
                          triggeredSentences =
                            map snd $ takeWhile ((<= tolerance_) . fst)
                              possiblyTriggeredSentences
                          nextSelectedSentences =
                            filter (isSelected sineResultAcc' gTheoryLid)
                              triggeredSentences
                          sineResultAcc'' =
                            foldr (selectPremise gTheoryLid) sineResultAcc'
                              nextSelectedSentences
                      in  selectPremises' opts tolerance_ depthLimitM
                            premiseLimitM (currentDepth + 1) gTheoryLid
                            extSign sineResultAcc'' nextSelectedSentences
                    )
                    sineResultAcc $
                    nub $ symsOfSen gTheoryLid sign $
                    sentence previouslySelectedNamedSentence
           ) sineResult previouslySelectedNamedSentences
  where
--    premiseTriggers' :: Map symbol [(Double, Named sentence)]
    premiseTriggers' =
      coercePremiseTriggers "selectPremises' 1" gSineLogic gTheoryLid premiseTriggers
--    selectedPremises' :: Set (Named sentence)
--    selectedPremises' =
--      coerce "selectPremises' 2" gSineLogic gTheoryLid selectedPremises

isSelected :: Logic.Logic lid sublogics basic_spec sentence symb_items
                          symb_map_items sign morphism symbol
                          raw_symbol proof_tree
           => G_SInEResult
           -> lid
           -> Named sentence
           -> Bool
isSelected G_SInEResult{..} gTheoryLid namedSentence =
  Set.member (senAttr namedSentence) selectedPremiseNames

selectPremise :: Logic.Logic lid sublogics basic_spec sentence symb_items
                             symb_map_items sign morphism symbol
                             raw_symbol proof_tree
              => lid
              -> Named sentence
              -> G_SInEResult
              -> G_SInEResult
selectPremise gTheoryLid triggeredSentence
  sineResult@G_SInEResult {..} =
  let symbolCommonnesses' =
        coerceSymbolCommonnesses "selectPremise 1" gSineLogic gTheoryLid symbolCommonnesses
      premiseTriggers' =
        coercePremiseTriggers "selectPremise 2" gSineLogic gTheoryLid premiseTriggers
      leastCommonSymbols' =
        coerceLeastCommonSymbols "selectPremise 3" gSineLogic gTheoryLid leastCommonSymbols
      selectedPremises' =
        coerceSelectedPremises "selectPremise 4" gSineLogic gTheoryLid selectedPremises
  in  G_SInEResult gTheoryLid parameters symbolCommonnesses' premiseTriggers'
        leastCommonSymbols' selectedPremises' selectedPremiseNames

saveToDatabase :: HetcatsOpts
               -> G_SInEResult
               -> Entity LocIdBase
               -> SinePremiseSelectionId
               -> IO ()
saveToDatabase opts G_SInEResult{..} omsEntity sinePremiseSelectionKey =
  onDatabase (databaseConfig opts) $ do
    saveSymbolPremiseTriggers
    saveSymbolCommonnesses
    return ()
  where
    saveSymbolPremiseTriggers =
      mapM_ (\ (symbol, triggers) -> do
              symbolKey <- fetchSymbolId symbol
              mapM_ (\ (minimalTolerance, namedSentence) -> do
                      premiseKey <- fetchSentenceId namedSentence
                      insert SineSymbolPremiseTrigger
                        { sineSymbolPremiseTriggerSinePremiseSelectionId = sinePremiseSelectionKey
                        , sineSymbolPremiseTriggerPremiseId = premiseKey
                        , sineSymbolPremiseTriggerSymbolId = symbolKey
                        , sineSymbolPremiseTriggerMinTolerance = minimalTolerance
                        }
                    ) triggers
            ) $ Map.toList premiseTriggers

    saveSymbolCommonnesses =
      mapM_ (\ (symbol, commonness) -> do
              symbolKey <- fetchSymbolId symbol
              insert SineSymbolCommonness
                { sineSymbolCommonnessSinePremiseSelectionId = sinePremiseSelectionKey
                , sineSymbolCommonnessSymbolId = symbolKey
                , sineSymbolCommonnessCommonness = commonness
                }
            ) $ Map.toList symbolCommonnesses

    fetchSymbolId symbol =
      let (locId, _, _, _) = symbolDetails omsEntity gSineLogic symbol
      in  fetchLocId locId "Symbol"

    fetchSentenceId namedSentence =
      let name = senAttr namedSentence
          locId = locIdOfSentence omsEntity name
      in  fetchLocId locId "Sentence"

    fetchLocId locId kind = do
      sentenceL <- select $ from $ \ loc_id_bases -> do
        where_ (loc_id_bases ^. LocIdBaseLocId ==. val locId)
        limit 1
        return loc_id_bases
      case sentenceL of
        [] -> fail ("Persistence.Reasoning.saveToDatabase: Could not find " ++ kind ++ " " ++ locId)
        Entity key _ : _ -> return key


coerceSymbolCommonnesses ::
   (Logic.Logic lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
   Logic.Logic lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2)
   => String -> lid1 -> lid2 -> Map symbol1 Int -> Map symbol2 Int
coerceSymbolCommonnesses errorMessage lid1 lid2 a =
  let errorMessage' =
        "PremiseSelectionSInE." ++ errorMessage ++ ": Coercion failed."
  in  fromMaybe (error errorMessage') $ primCoerce lid1 lid2 errorMessage' a

coerceLeastCommonSymbols ::
   (Logic.Logic lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
   Logic.Logic lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2)
   => String -> lid1 -> lid2 
         -> Map (Named sentence1) (symbol1, Int)
         -> Map (Named sentence2) (symbol2, Int)
coerceLeastCommonSymbols errorMessage lid1 lid2 a =
  let errorMessage' =
        "PremiseSelectionSInE." ++ errorMessage ++ ": Coercion failed."
  in  fromMaybe (error errorMessage') $ primCoerce lid1 lid2 errorMessage' a

coercePremiseTriggers ::
   (Logic.Logic lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
   Logic.Logic lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2)
   => String -> lid1 -> lid2 
         -> Map symbol1 [(Double, Named sentence1)]
         -> Map symbol2 [(Double, Named sentence2)]
coercePremiseTriggers errorMessage lid1 lid2 a =
  let errorMessage' =
        "PremiseSelectionSInE." ++ errorMessage ++ ": Coercion failed."
  in  fromMaybe (error errorMessage') $ primCoerce lid1 lid2 errorMessage' a

coerceSelectedPremises ::
   (Logic.Logic lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
   Logic.Logic lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2)
   => String -> lid1 -> lid2 -> Set (Named sentence1) -> Set (Named sentence2)
coerceSelectedPremises errorMessage lid1 lid2 a =
  let errorMessage' =
        "PremiseSelectionSInE." ++ errorMessage ++ ": Coercion failed."
  in  fromMaybe (error errorMessage') $ primCoerce lid1 lid2 errorMessage' a

coerceSen ::
   (Logic.Logic lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
   Logic.Logic lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2)
   => String -> lid1 -> lid2 -> Named sentence1 -> Named sentence2
coerceSen errorMessage lid1 lid2 a =
  let errorMessage' =
        "PremiseSelectionSInE." ++ errorMessage ++ ": Coercion failed."
  in  fromMaybe (error errorMessage') $ primCoerce lid1 lid2 errorMessage' a

