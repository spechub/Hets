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

import qualified OWL2.AS as AS
import OWL2.Sign
import OWL2.MS

import Common.AS_Annotation
import Common.IRI as IRI
import Common.Id (stringToId)
import Common.Result

import Data.Maybe
import qualified Data.Set as Set

data Medusa = Medusa {
               indivs :: Set.Set (IRI, IRI),
               relations :: Set.Set (IRI, IRI, IRI, IRI)}

-- | given an OWL ontology (iri and theory), compute the medusa data
medusa :: IRI.IRI -> (Sign, [Named AS.Axiom])
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


getClass :: [AS.Axiom] -> IRI -> IRI
getClass axs ind = 
  let n = nullIRI { iriPath = stringToId "unknown", isAbbrev = True }
      f ax = case ax of
        AS.Assertion (AS.ClassAssertion _ (AS.Expression clIri) indIri) | indIri == ind -> Just clIri
        _ -> Nothing
  in
    fromMaybe n $ checkMapMaybe f axs

--  for each individual "p1" that has a fact "meets p2"
--  look for individuals "i1" and "i2" such that
--  i1 has_fiat_boundary p1 and i2 has_fiat_boundary p2
--  and return i1 type(p1) i2 type(p2)
getMeetsFacts :: [AS.Axiom] -> Set.Set (IRI, IRI) -> IRI ->
              Set.Set (IRI, IRI, IRI, IRI)
getMeetsFacts axs tInds n =
  Set.fromList $ mapMaybe (getMeetsFactsAux axs tInds n) axs

getMeetsFactsAux :: [AS.Axiom] -> Set.Set (IRI, IRI) -> IRI -> AS.Axiom ->
                 Maybe (IRI, IRI, IRI, IRI)
getMeetsFactsAux axs tInds point1 ax = case ax of
  AS.Assertion (AS.ObjectPropertyAssertion _ (AS.ObjectProp ope) sInd tInd)
    | show (iriPath ope) == "meets" &&
      point1 == sInd -> getFiatBoundaryFacts axs tInds sInd tInd
  _ -> Nothing


getFiatBoundaryFacts :: [AS.Axiom] -> Set.Set (IRI, IRI) -> IRI -> IRI ->
                     Maybe (IRI, IRI, IRI, IRI)
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

getFiatBoundaryFactsAux :: IRI -> AS.Axiom -> Maybe IRI
getFiatBoundaryFactsAux point ax = case ax of
  AS.Assertion (AS.ObjectPropertyAssertion _ (AS.ObjectProp ope) sInd tInd)
    | show (iriPath ope) == "has_fiat_boundary" && 
      (iriPath point == iriPath tInd) -> Just sInd
  _ -> Nothing


-- | retrieve the first class of list, somewhat arbitrary
firstClass :: AnnotatedList AS.ClassExpression -> Maybe IRI
firstClass ((_,AS.Expression c):_) = Just c
firstClass _ = Nothing
