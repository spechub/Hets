{- | Module     : $Header$
 -  Description : Abstract syntax for the Compositional Modal Prover
 -  Copyright   : (c) Georgel Calin & Lutz Schroeder, DFKI Lab Bremen
 -  License     : Similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
 -  Maintainer  : g.calin@jacobs-alumni.de
 -  Stability   : provisional
 -  Portability : non-portable (various -fglasgow-exts extensions)
 -
 -  Provides data structures used by the Compositional Prover -}
{-# OPTIONS -fglasgow-exts #-}
module CompAS where

--import Debug.Trace
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.List as List

-- | Datatype for holding modal formulae of a certain type
data Boole a = F | T | And (Boole a) (Boole a) | Or (Boole a) (Boole a) | 
               Not (Boole a) | At a deriving (Eq, Ord, Show)

-- | Datatype for a modal formulae of type "l" wrapped under K modal logic
data K l = K (Boole l) deriving (Eq, Ord, Show)
-- | Datatype for the "rules" of K modal logic
data RK = RK Int deriving Show
-- | Datatype for a modal formulae of type "l" wrapped under KD modal logic
data KD l  = KD (Boole l) deriving (Eq, Ord, Show)
-- | Datatype for the "rules" of KD modal logic
data RKD = RKDPos Int | RKDNeg Int deriving Show
-- | Datatype for combined Segala logics
data Segala a = S (KD (K (Segala a))) deriving (Eq, Show)
-- | Datatype for propositional clauses
data Clause a = Implies (Set.Set a) (Set.Set a) deriving (Eq, Ord, Show)
-- | Datatype for substitutions
data Subst a = Subst (Map.Map Int a) deriving (Eq, Show)

-- | Logic Class
class Logic a b | a -> b, b -> a where
  match :: Clause (a c) -> [(b, Subst (Boole c))]
  clauses :: b -> [Clause Int]
  subclauses :: Ord c => Clause (a c) -> Set.Set (Clause (a c))
-- | Logic instance for K modal logic
instance Logic K RK where
  match ((Implies n p)::Clause (K c)) = 
    let i = Set.size n
        strip (K x) = x
        substHead = (i+1,strip(head(Set.elems p)))
        substTail = zip [1..i] (map strip (Set.elems n))
    in [(RK i, Subst (Map.fromList (substHead:substTail)))]
  clauses (RK n) = [Implies (Set.fromList [1..n]) (Set.singleton (n+1))]
  subclauses (Implies n p) = 
    Set.fromList [Implies n (Set.singleton l) | l <- Set.elems p]
-- | Logic instance for KD modal logic
instance Logic KD RKD where
  match ((Implies n p):: Clause (KD c)) = 
    let i = Set.size n 
        strip (KD x) = x
        substHead = (i+1,strip(head(Set.elems p)))
        substTail = zip [1..i] (map strip (Set.elems n))
    in [(RKDPos i, Subst (Map.fromList (substHead:substTail)))]
  clauses (RKDPos n) = 
    case n of
      0 -> [Implies (Set.empty) (Set.singleton 1)]
      _ -> [Implies (Set.fromList [1..n]) (Set.singleton (n+1))]
  clauses (RKDNeg n) = [Implies (Set.fromList [1..n]) (Set.empty)]
  subclauses (Implies n p) = 
    Set.fromList [Implies n (Set.singleton l) | l <- Set.elems p]

