{- |
Module      :  $Header$
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
import Common.Id
import Common.IRI as IRI
import Common.DocUtils
import Common.Result
import qualified Common.Lib.Rel as Rel

import Data.Maybe
import qualified Data.Set as Set

import Debug.Trace

data Medusa = Medusa { 
               indivs :: Set.Set (QName,QName),
               relations :: Set.Set (QName, QName, QName, QName)}

-- | given an OWL ontology (iri and theory), compute the medusa data
medusa :: IRI.IRI -> (Sign, [Named Axiom])
                       -> Result Medusa
medusa _ (sig, nsens) = do
  let inds = individuals sig
      getC = getClass (map sentence nsens)
      getR = getMeetsFacts (map sentence nsens)
  return $ Medusa {
            indivs = Set.map (\ i -> (i,getC i)) inds, 
            relations = -- trace ("nsens:" ++ (concatMap (\x -> show (sentence x) ++ "\n") nsens)) $ 
                        foldl Set.union Set.empty $ map getR $ Set.toList inds
           }

-- | get the class of an individual
getClass :: [Axiom] -> QName -> QName
getClass axs n = case mapMaybe (getClassAux n) axs of
   (c:_) -> c
   [] -> nullQName { localPart = "unknown" }

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
--  and return i1 p1 i2 p2
getMeetsFacts :: [Axiom] -> QName -> Set.Set (QName, QName, QName, QName)
getMeetsFacts axs n = case mapMaybe (getMeetsFactsAux axs n) axs of
   [] -> Set.empty
   x -> Set.fromList x

getMeetsFactsAux :: [Axiom] -> QName -> Axiom -> Maybe (QName, QName, QName, QName)
getMeetsFactsAux axs point1 ax = 
  case axiomTopic ax of
    SimpleEntity e | cutIRI e == point1 ->
      case axiomBit ax of
         ListFrameBit Nothing (IndividualFacts [([], (ObjectPropertyFact Positive (ObjectProp ope) point2))]) -> 
            if localPart ope == "meets" then trace ("point1:"++ show point1 ++ "point2:" ++ show point2 ++"\n") $  getFiatBoundaryFacts axs point1 point2
              else Nothing
         _ -> Nothing
    _ -> Nothing

getFiatBoundaryFacts :: [Axiom] -> QName -> QName -> Maybe (QName, QName, QName, QName)
getFiatBoundaryFacts axs point1 point2 = 
   let i1 = case mapMaybe (getFiatBoundaryFactsAux point1) axs of
              (c:_) -> Just c
              [] -> Nothing     
       i2 = case mapMaybe (getFiatBoundaryFactsAux point2) axs of
              (c:_) -> Just c
              [] -> Nothing
   in case (i1, i2) of
        (Just ind1, Just ind2) -> Just (ind1, point1, ind2, point2)
        _ -> Nothing

getFiatBoundaryFactsAux :: QName -> Axiom -> Maybe QName
getFiatBoundaryFactsAux point ax = trace ("point:" ++ show point ++ "\n")$
  case axiomTopic ax of 
    SimpleEntity e -> 
      case axiomBit ax of
       ListFrameBit Nothing (IndividualFacts [([], (ObjectPropertyFact Positive (ObjectProp ope) point'))]) -> 
         if (localPart ope == "has_fiat_boundary") && (localPart point == localPart point') then trace (show ax) $ Just $ cutIRI e
           else Nothing
       _ -> Nothing
    _ -> Nothing
    

-- | retrieve the first class of list, somewhat arbitrary 
firstClass :: AnnotatedList ClassExpression -> Maybe QName
firstClass ((_,Expression c):_) = Just c
firstClass _ = Nothing
