{-# OPTIONS -fglasgow-exts #-}
module Comp where

--import Debug.Trace
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.List as List

data Boole a = F | T | And (Boole a) (Boole a) | Or (Boole a) (Boole a) | 
               Not (Boole a) | At a deriving (Eq, Ord, Show)

data K l = K (Boole l) deriving (Eq, Ord, Show)

data RK = RK Int deriving Show

data KD l  = KD (Boole l) deriving (Eq, Ord, Show)

data RKD = RKDPos Int | RKDNeg Int deriving Show

data Segala a = S (KD (K (Segala a))) deriving (Eq, Show)

data Clause a = Implies (Set.Set a) (Set.Set a) deriving (Eq, Ord, Show)

data Subst a = Subst (Map.Map Int a) deriving (Eq, Show)

class Logic a b | a -> b, b -> a where
  match :: Clause (a c) -> [(b, Subst (Boole c))]
  clauses :: b -> [Clause Int]
  subclauses :: Ord c => Clause (a c) -> Set.Set (Clause (a c))

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

-- testing Segala
data KDK = KDK deriving Show
test = S (KD (Or (At (K (And (At (S (KD T))) F))) (Or F (At (K F)))))::Segala KDK

-- modal atoms
ma :: Eq a => Boole a -> [Boole a]
ma it = 
  case it of
    F           -> []
    T           -> []
    And phi psi -> (ma phi) `List.union` (ma psi)
    Or phi psi  -> (ma phi) `List.union` (ma psi)
    Not phi     -> ma phi
    --M a phi     -> [M a phi]
    At a        -> [At a]

--matest = ma ((\(S (KD x)) -> x) test)

-- subst :: (Logic a b) => Boole a -> Clause a -> Boole a
subst :: Boole a -> c -> Boole b
subst it s =
  case it of
    And phi psi -> And (subst phi s) (subst psi s)
    Or phi psi  -> Or (subst phi s) (subst psi s)
    Not phi     -> Not (subst phi s)
    T           -> T
    F           -> F
{-
phi (Clause (pos, neg))
  | elem phi neg = F
  | elem phi pos = T    
-}

--eval :: Eq a => Boole a -> Bool
eval :: Boole a -> Bool
eval it = 
  case it of
    T           -> True
    F           -> False
    Not phi     -> not (eval phi)
    Or phi psi  -> (eval phi) || (eval psi)
    And phi psi -> (eval phi) && (eval psi)

-- dnf
--allsat :: (Logic a b) => Boole a -> [Clause a]
allsat :: (Eq t, Logic a [Boole t]) => Boole t -> [Clause Int]
allsat phi = filter (\x -> eval (subst phi x)) (clauses (ma phi))

-- cnf
--cnf :: (Logic a b) => Boole a -> [Clause a]
cnf :: (Eq t, Logic a [Boole t]) => Boole t -> [Clause Int]
cnf phi = map (\(Implies x y) -> (Implies y x)) (allsat (Not phi))

-- proof search
-- phi is provable iff all members of its CNF have a provable matching
-- also any matching is in general a cnf and all of its clauses must hold
--provable :: (Logic a b) => Boole a -> Bool
--provable phi = all (\c -> any (all provable) (match c)) (cnf phi)
