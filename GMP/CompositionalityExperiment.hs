{-# OPTIONS -fglasgow-exts #-}
module Comp where

import Debug.Trace
import qualified Data.Set as Set
import qualified Data.Map as Map

data Boole a = F | T | And (Boole a) (Boole a) | Or (Boole a) (Boole a) | 
     	      Not (Boole a) | At a deriving (Eq, Show)

data K l = K (Boole l) deriving (Eq, Show)

data RK = RK Int deriving Show

data KD l  = KD (Boole l) deriving (Eq, Show)

data RKD = RKDPos Int | RKDNeg Int deriving Show

data Segala a = S (Boole (KD (K (Segala a)))) deriving (Eq, Show)

data Clause a = Implies (Set.Set a) (Set.Set a) deriving Show

data Subst a = Subst (Map.Map Int a) deriving Show

class Logic a b | a -> b, b -> a where
  match :: Clause (a c) -> [(b, Subst (a c))]
  clauses :: b -> [Clause Int]
  subclauses :: Ord(Clause (a c)) => Clause (a c) -> Set.Set (Clause (a c))

instance Logic K RK where
  match ((Implies n p)::Clause (K c)) = 
    let i = Set.size n in
    [(RK i, Subst (Map.fromList 
    ((i+1,head (Set.elems p)): zip [1..i] (Set.elems n))))]
  clauses (RK n) = [Implies (Set.fromList [1..n]) (Set.singleton (n+1))]
  subclauses (Implies n p) = Set.fromList [Implies n (Set.singleton l) | l <- Set.elems p]

instance Logic KD RKD where
  match ((Implies n p):: Clause (KD c)) = 
    let i = Set.size n in
    [(RKDPos i, Subst (Map.fromList 
  	((i+1,head (Set.elems p)): zip [1..i] (Set.elems n))))]
  clauses (RKDPos n) = [Implies (Set.fromList [1..n]) (Set.singleton (n+1))]
  clauses (RKDNeg n) = [Implies (Set.fromList [1..n]) (Set.singleton (n+1))]
  subclauses (Implies n p) = Set.fromList [Implies n (Set.singleton l) | l <- Set.elems p]
