
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  All rights reserved.

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable
    
supply a simple data type for precedence or subsort relations 
based on a (hidden) map of sets 

'Rel a' replaces a directed graph with unique node labels (Ord a) and
unlabelled edges (without multiplicity higher than one).

Usage: start with an 'empty' relation, 'insert' edges, and test for
an edge 'member' (before or after calling 'transClosure'). 

It is possible to insert self edges or bigger cycles.

A transitive path can be checked by 'transMember' without computing
the full transitive closure. A further 'insert', however,
may destroy the closedness property of a relation.

Currently, no further functions seem to be necessary: 
- reflexive closure 
- filtering, mapping
- deletion
- computing a minimal relation whose transitive closure 
  covers a given relation 

-}

module Common.Lib.Rel (Rel(), empty, isEmpty, insert, member
		      , transMember, transClosure) where

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set

newtype Rel a = Rel { toMap :: Map.Map a (Set.Set a) } deriving Show

empty :: Rel a
empty = Rel Map.empty

isEmpty :: Rel a -> Bool
isEmpty = Map.isEmpty . toMap 

insert :: Ord a => a -> a -> Rel a -> Rel a
-- order matters!
insert a b =
    let update m = Map.insert a ((b `Set.insert`) $ 
				 Map.findWithDefault Set.empty a m) m
    in 
    Rel . update .toMap

member :: Ord a => a -> a -> Rel a -> Bool
member a b r = Set.member b $ getDAdjs r a

getDAdjs :: Ord a => Rel a -> a -> Set.Set a
-- direct neighbours
getDAdjs r a = Map.findWithDefault Set.empty a $ toMap r

getTAdjs :: Ord a => Rel a -> Set.Set a -> Set.Set a -> Set.Set a
-- transitive neighbours
-- initial call 'getTAdjs succs r Set.empty $ Set.single a'
getTAdjs r given new =
    if Set.isEmpty new then given else 
    let ds = Set.unions $ map (getDAdjs r) $ Set.toList new in 
    getTAdjs r (ds `Set.union` given) (ds Set.\\ new Set.\\ given)

transMember :: Ord a => a -> a -> Rel a -> Bool
transMember a b r = Set.member b $ getTAdjs r Set.empty $ Set.single a

transClosure ::  Ord a => Rel a -> Rel a
transClosure r = Rel $ Map.map ( \ s -> getTAdjs r s s) $ toMap r
