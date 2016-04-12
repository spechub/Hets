{- |
Module      :  ./OWL2/Medusa.hs
Description :  Convert OWL2 ontology to Medusa data structure
Copyright   :  (c) Till Mossakowski, Uni Magdeburg 2016
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  till@iws.cs.ovgu.de
Stability   :  provisional
Portability :  portable

Convert an OWL2 ontology to Medusa data structure,
see https://github.com/ConceptualBlending/monster_render_system
-}

module OWL2.Medusa where

import OWL2.AS
import OWL2.Sign
import OWL2.MS

import Common.AS_Annotation
import Common.IRI as IRI
import Common.Result

import Data.Maybe
import qualified Data.Set as Set

data Medusa = Medusa {
               indivs :: Set.Set (QName,QName),
               relations :: Set.Set (QName, QName, QName, QName)}

-- | given an OWL ontology (iri and theory), compute the medusa data
medusa :: IRI.IRI -> (Sign, [Named Axiom])
                       -> Result Medusa
medusa _ (sig, nsens) = do
  let inds = individuals sig
      getC = getClass (map sentence nsens)
      getR tInds = getMeetsFacts (map sentence nsens) tInds
      allInds = Set.map (\ i -> (i,getC i)) inds
      relTuples = foldl Set.union Set.empty $
                  map (getR allInds) $ Set.toList inds
      images = Set.foldl Set.union Set.empty $
               Set.map (\(i1, _, i2, _) -> Set.fromList [i1, i2]) relTuples
  return $ Medusa {
            indivs = Set.filter (\(i,_) -> Set.member i images) allInds ,
            relations = relTuples
           }

checkMapMaybe :: (a -> Maybe b) -> [a] -> Maybe b
checkMapMaybe f x =
 case mapMaybe f x of
   (c:_) -> Just c
   [] -> Nothing

-- | get the class of an individual
getClass :: [Axiom] -> QName -> QName
getClass axs n = case checkMapMaybe (getClassAux n) axs of
   Just c -> c
   Nothing -> nullQName { localPart = "unknown" }

getClassAux :: QName -> Axiom -> Maybe QName
getClassAux ind ax =
  case axiomTopic ax of
    SimpleEntity e | cutIRI e == ind ->
      case axiomBit ax of
         ListFrameBit (Just Types) (ExpressionBit classes) -> firstClass classes
         _ -> Nothing
    _ -> Nothing

--  for each individual "p1" that has a fact "meets p2"
--  look for individuals "i1" and "i2" such that
--  i1 has_fiat_boundary p1 and i2 has_fiat_boundary p2
--  and return i1 type(p1) i2 type(p2)
getMeetsFacts :: [Axiom] -> Set.Set (QName, QName) -> QName ->
              Set.Set (QName, QName, QName, QName)
getMeetsFacts axs tInds n =
  Set.fromList $ mapMaybe (getMeetsFactsAux axs tInds n) axs

getMeetsFactsAux :: [Axiom] -> Set.Set (QName, QName) -> QName -> Axiom ->
                 Maybe (QName, QName, QName, QName)
getMeetsFactsAux axs tInds point1 ax =
  case axiomTopic ax of
    SimpleEntity e | cutIRI e == point1 ->
      case axiomBit ax of
         ListFrameBit Nothing (IndividualFacts [([],
                               (ObjectPropertyFact Positive
                                                   (ObjectProp ope) point2))
                                               ]) ->
            if localPart ope == "meets" then
                getFiatBoundaryFacts axs tInds point1 point2
              else Nothing
         _ -> Nothing
    _ -> Nothing

getFiatBoundaryFacts :: [Axiom] -> Set.Set (QName, QName) -> QName -> QName ->
                     Maybe (QName, QName, QName, QName)
getFiatBoundaryFacts axs tInds point1 point2 =
   let i1 = checkMapMaybe (getFiatBoundaryFactsAux point1) axs
       i2 = checkMapMaybe (getFiatBoundaryFactsAux point2) axs
       typeOf ind =
         case Set.toList $ Set.filter (\(x, _) -> x == ind) tInds of
           [(_, t)] -> t
           _ -> error $ "could not determine the type of " ++ show ind
   in case (i1, i2) of
        (Just ind1, Just ind2) ->
           Just (ind1, typeOf point1, ind2, typeOf point2)
        _ -> Nothing

getFiatBoundaryFactsAux :: QName -> Axiom -> Maybe QName
getFiatBoundaryFactsAux point ax =
  case axiomTopic ax of
    SimpleEntity e ->
      case axiomBit ax of
       ListFrameBit Nothing (IndividualFacts facts) ->
        loopFacts facts e point
       _ -> Nothing
    _ -> Nothing


loopFacts :: AnnotatedList Fact -> Entity -> QName -> Maybe QName
loopFacts [] _ _ = Nothing
loopFacts (afact:facts') e point =
  case afact of
    ([], (ObjectPropertyFact Positive (ObjectProp ope) point')) ->
      if (localPart ope == "has_fiat_boundary") &&
         (localPart point == localPart point') then Just $ cutIRI e
       else loopFacts facts' e point
    _ -> loopFacts facts' e point


-- | retrieve the first class of list, somewhat arbitrary
firstClass :: AnnotatedList ClassExpression -> Maybe QName
firstClass ((_,Expression c):_) = Just c
firstClass _ = Nothing
