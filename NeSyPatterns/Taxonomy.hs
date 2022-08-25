{- |
Module      :  ./NeSyPatterns/Taxonomy.hs
Description :  Taxonomy extraction for NeSyPatterns
Copyright   :  (c) Dominik Luecke, Uni Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portabl

Taxonomy extraction for NeSyPatterns
-}

module NeSyPatterns.Taxonomy ( nesy2Tax ) where

import NeSyPatterns.Sign

import Common.Id

import Common.AS_Annotation
import Common.Result
import Taxonomy.MMiSSOntology
import Common.Taxonomy

import qualified Data.Foldable as Fold
import qualified Data.Relation as Rel

import qualified Data.Map as Map

import qualified Data.Set as Set

-- | Derivation of an Taxonomy for NeSyPatterns
nesy2Tax :: TaxoGraphKind
         -> MMiSSOntology
         -> Sign -> [Named ()]
         -> Result MMiSSOntology
nesy2Tax gk inOnto sig _ = case gk of
  KSubsort -> fail "Dear user, this logic is single sorted, sorry!"
  KConcept -> makeMiss inOnto (edges sig) (nodes sig)


-- | Generation of a MissOntology
makeMiss :: MMiSSOntology
         -> Rel.Relation ResolvedNode ResolvedNode
         -> Set.Set ResolvedNode
         -> Result MMiSSOntology
makeMiss o relation = let 
    superClasses y = fmap (show . pretty) . Set.toList . Rel.lookupRan y $ relation
  in Fold.foldlM (\o' y -> fromWithError $ insertClass o' (show $ pretty y) "" (superClasses y) Nothing) o
