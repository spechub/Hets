module Persistence.Reasoning.PremiseSelectionSInE ( SInEResult (..)
                                                  , SInEParameters (..)
                                                  , perform
                                                  ) where

import PGIP.ReasoningParameters as ReasoningParameters

import Common.AS_Annotation
import Common.ExtSign
import Common.LibName
import qualified Common.OrderedMap as OMap
import Common.Timing (measureWallTime)
import Driver.Options
import Logic.Grothendieck
import Logic.Logic
import Static.DevGraph
import Static.GTheory

import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Time.LocalTime
import Data.Time.Clock

data SInEResult symbol sentence =
  SInEResult { parameters :: SInEParameters
             , symbolCommonnesses :: Map symbol Int
             , premiseTriggers :: Map symbol [(Double, Named sentence)] -- this list is ordered by the Double
             , leastCommonSymbols :: Map (Named sentence) (symbol, Int)
             , selectedPremises :: Set (Named sentence)
             , selectedPremiseNames :: Set String
             } deriving Show

data SInEParameters = SInEParameters { depthLimit :: Maybe Int
                                     , tolerance :: Maybe Double
                                     , premiseNumberLimit :: Maybe Int
                                     } deriving Show

perform :: Logic lid sublogics basic_spec sentence symb_items
                 symb_map_items sign morphism symbol
                 raw_symbol proof_tree
        => HetcatsOpts
        -> LibEnv
        -> LibName
        -> DGraph
        -> (Int, DGNodeLab)
        -> G_theory
        -> G_sublogics
        -> ReasoningParameters.PremiseSelection
        -> String
        -> IO (Maybe [String], Int, SInEResult symbol sentence)
perform opts libEnv libName dGraph nodeLabel gTheory gSublogics
  premiseSelectionParameters goalName = do
  let parameters_ = SInEParameters
        { depthLimit = ReasoningParameters.sineDepthLimit reasoningParameters
        , tolerance = ReasoningParameters.sineTolerance reasoningParameters
        , premiseNumberLimit = ReasoningParameters.sinePremiseNumberLimit reasoningParameters
        }
  let sineResult0 = SInEResult
        { parameters = parameters_
        , symbolCommonnesses = Map.empty
        , premiseTriggers = Map.empty
        , leastCommonSymbols = Map.empty
        , selectedPremises = Set.empty
        , selectedPremiseNames = Set.empty
        }
  (premisesM, wallTimeOfDay) <- measureWallTime $ do
    let (sineResult1, goal) =
          preprocess opts libEnv libName dGraph nodeLabel gTheory gSublogics
            sineResult0 goalName
    let sineResult2 =
          selectPremises opts libEnv libName dGraph nodeLabel gTheory gSublogics
            sineResult1 goal
    let premisesM =
         Just $ Set.toList $ Set.map senAttr $ selectedPremises sineResult2
    return premisesM
  return ( premisesM
         , timeToTimeOfDay $ secondsToDiffTime $ toInteger wallTimeOfDay
         )

preprocess :: Logic lid sublogics basic_spec sentence symb_items
                    symb_map_items sign morphism symbol
                    raw_symbol proof_tree
           => HetcatsOpts
           -> LibEnv
           -> LibName
           -> DGraph
           -> (Int, DGNodeLab)
           -> G_theory
           -> G_sublogics
           -> SInEResult symbol sentence
           -> String
           -> (SInEResult symbol sentence, Named sentence)
preprocess opts libEnv libName dGraph nodeLabel G_theory { gTheoryLogic = lid, gTheorySens = sentences, gTheorySign = sign } gSublogics sineResult0 goalName =
  let namedSentences = map (uncurry toNamed) $ OMap.toList sentences
      goal = fromJust $ find ((goalName ==) . senAttr) namedSentences
      sineResult1 = computeSymbolCommonnesses lid sign sineResult0 namedSentences
      sineResult2 = computeLeastCommonSymbols lid sign sineResult1 namedSentences
      sineResult3 = computePremiseTriggers lid sign sineResult1 namedSentences
  in  (sineResult3, goal)

computeSymbolCommonnesses :: Logic lid sublogics basic_spec sentence symb_items
                                   symb_map_items sign morphism symbol
                                   raw_symbol proof_tree
                          => lid
                          -> ExtSign sign symbol
                          -> SInEResult symbol sentence
                          -> [Named sentence]
                          -> SInEResult symbol sentence
computeSymbolCommonnesses lid sign sineResult0 namedSentences =
  let result =
        foldr (\ namedSentence symbolCommonnessesAcc ->
                foldr (\ symbol symbolCommonnessesAcc' ->
                        Map.insertWith (+) symbol 1 symbolCommonnessesAcc'
                      ) symbolCommonnessesAcc $ nub $ symsOfSen lid sign $ sentence namedSentence
              ) (symbolCommonnesses sineResult0) namedSentences
  in  sineResult0 { symbolCommonnesses = result }

computeLeastCommonSymbols :: Logic lid sublogics basic_spec sentence symb_items
                                   symb_map_items sign morphism symbol
                                   raw_symbol proof_tree
                          => lid
                          -> ExtSign sign symbol
                          -> SInEResult symbol sentence
                          -> [Named sentence]
                          -> SInEResult symbol sentence
computeLeastCommonSymbols lid sign sineResult0 namedSentences =
  let result =
        foldr (\ namedSentence leastCommonSymbolsAcc ->
                foldr (\ symbol leastCommonSymbolsAcc' ->
                        let commonness = fromJust $ Map.lookup symbol $
                              symbolCommonnesses sineResult0
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
                      nub $ symsOfSen lid sign $ sentence namedSentence
              ) (leastCommonSymbols sineResult0) namedSentences
  in  sineResult0 { leastCommonSymbols = result }

computePremiseTriggers :: Logic lid sublogics basic_spec sentence symb_items
                                symb_map_items sign morphism symbol
                                raw_symbol proof_tree
                       => lid
                       -> ExtSign sign symbol
                       -> SInEResult symbol sentence
                       -> [Named sentence]
                       -> SInEResult symbol sentence
computePremiseTriggers lid sign sineResult0 namedSentences =
  let commonnesses = symbolCommonnesses sineResult0
      leastCommonSymbols_ = leastCommonSymbols sineResult0
      result =
        foldr (\ namedSentence premiseTriggersAcc ->
                let (_, leastCommonness) = fromJust $
                      Map.lookup namedSentence leastCommonSymbols_
                in  foldr (\ symbol premiseTriggersAcc' ->
                            let symbolCommonness = fromJust $
                                  Map.lookup symbol commonnesses
                                minimalTolerance =
                                  symbolCommonnesses / leastCommonness
                            in  Map.insertWith
                                  (\ _ triggers ->
                                    insertBy
                                      (compare . fst)
                                      (minimalTolerance, namedSentence)
                                      triggers
                                  )
                                  symbol
                                  [(minimalTolerance, namedSentence)]
                                  premiseTriggersAcc'
                          )
                          premiseTriggersAcc $
                          nub $ symsOfSen lid sign $ sentence namedSentence
              ) (premiseTriggers sineResult0) namedSentences
  in  sineResult0 { premiseTriggers = result }

selectPremises :: Logic lid sublogics basic_spec sentence symb_items
                        symb_map_items sign morphism symbol
                        raw_symbol proof_tree
               => HetcatsOpts
               -> LibEnv
               -> LibName
               -> DGraph
               -> (Int, DGNodeLab)
               -> G_theory
               -> G_sublogics
               -> SInEResult symbol sentence
               -> Named sentence
               -> SInEResult symbol sentence
selectPremises opts libEnv libName dGraph nodeLabel gTheory gSublogics sineResult0 goal =
  let premiseLimitM = premiseNumberLimit $ parameters sineResult0
      depthLimitM = depthLimit $ parameters sineResult0
      tolerance = fromMaybe 1.0 $ tolerance $ parameters sineResult0
  in  selectPremises' opts tolerance depthLimitM premiseLimitM 0 sineResult0 [goal]

selectPremises' :: Logic lid sublogics basic_spec sentence symb_items
                         symb_map_items sign morphism symbol
                         raw_symbol proof_tree
                => HetcatsOpts
                -> Double
                -> Maybe Int
                -> Maybe Int
                -> Int
                -> SInEResult symbol sentence
                -> [Named sentence]
                -> SInEResult symbol sentence
selectPremises' opts tolerance depthLimitM premiseLimitM currentDepth
  sineResult@SInEResult { premiseTriggers = premiseTriggers_
                        , selectedPremises = selectedPremises_
                        } =
  if isJust depthLimitM && currentDepth >= fromJust depthLimitM
  then sineResult
  else if isJust premiseLimitM && Set.size selectedPremises_ >= fromJust premiseLimitM
  then sineResult
  else foldr (\ previouslySelectedNamedSentence sineResultAcc ->
                foldr (\ symbol sineResultAcc' ->
                        let possiblyTriggeredSentences =
                              fromJust $ Map.lookup symbol premiseTriggers_
                            triggeredSentences =
                              map snd $ takeWhile ((<= tolerance) . fst)
                                possiblyTriggeredSentences
                            nextSelectedSentences =
                              filter (isSelected sineResultAcc'') triggeredSentences
                            sineResult' =
                              foldr selectPremise sineResultAcc' nextSelectedSentences
                        in  selectPremises' opts tolerance depthLimitM
                              premiseLimitM (currentDepth + 1) sineResult'
                              nextSelectedSentences
                      )
                      sineResultAcc $
                      nub $ symsOfSen lid sign $ sentence previouslySelectedNamedSentence
             ) sineResult

isSelected :: Logic lid sublogics basic_spec sentence symb_items
                    symb_map_items sign morphism symbol
                    raw_symbol proof_tree
           => SInEResult symbol sentence
           -> Named sentence
           -> Bool
isSelected sineResult namedSentence =
  Set.member (senAttr namedSentence) $ selectedPremiseNames sineResult

selectPremise :: Logic lid sublogics basic_spec sentence symb_items
                       symb_map_items sign morphism symbol
                       raw_symbol proof_tree
              => Named sentence
              -> SInEResult symbol sentence
              -> SInEResult symbol sentence
selectPremise triggeredSentence
  sineResult@SInEResult { selectedPremises = selectedPremises_
                        , selectedPremiseNames = selectedPremiseNames_
                        } =
  sineResult { selectedPremises = Set.insert triggeredSentence selectedPremises_
             , selectedPremiseNames =
                 Set.insert (senAttr triggeredSentence) selectedPremiseNames_
             }
