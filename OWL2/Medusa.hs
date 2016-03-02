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


data Medusa = Medusa { indivs :: (Set.Set (QName,QName)) }

-- | given an OWL ontology (iri and theory), compute the medusa data
medusa :: IRI.IRI -> (Sign, [Named Axiom])
                       -> Result Medusa
medusa iri (sig, nsens) = do
  let inds = individuals sig
      getC = getClass (map sentence nsens)
  return $ Medusa $ Set.map (\ i -> (i,getC i)) inds

-- | get the class of an individual
getClass :: [Axiom] -> QName -> QName
getClass axs n = case mapMaybe (getClassAux n) axs of
   (c:_) -> c
   [] -> QN { localPart = "unknown" }

getClassAux :: QName -> Axiom -> Maybe QName
getClassAux ind ax =
  case axiomTopic ax of
    SimpleEntity e | cutIRI e == ind ->
      case axiomBit ax of
         ListFrameBit (Just Types) (ExpressionBit classes) -> firstClass classes
         _ -> Nothing
    _ -> Nothing

-- | retrieve the first class of list, somewhat arbitrary
firstClass :: AnnotatedList ClassExpression -> Maybe QName
firstClass ((_,Expression c):_) = Just c
firstClass _ = Nothing
