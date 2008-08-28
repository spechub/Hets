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
module ModalLogic where

import qualified Data.Map as Map

-- | Datatype for holding modal formulae of a certain type
data Boole a = F | T | Not (Boole a) | And (Boole a) (Boole a) | At a 
  deriving (Eq, Ord, Show)

-- | Datatype for a modal formulae of type "l" wrapped under K modal logic
data K l = K (Boole l) deriving (Eq, Ord, Show)
-- | Datatype for the "rules" of K modal logic
data RK = RK Int deriving Show
-- | Datatype for a modal formulae of type "l" wrapped under KD modal logic
data KD l  = KD (Boole l) deriving (Eq, Ord, Show)
-- | Datatype for the "rules" of KD modal logic
data RKD = RKDPos Int | RKDNeg Int deriving Show
-- | Datatype for a modal formulae of type "l" wrapped under Graded ML
data G l = G Int (Boole l) deriving (Eq, Ord, Show)
-- | Datatype for the "rules" of Graded ML
data RG = RG [Int] [Int] deriving Show

-- | Datatype for combined Segala logics
--data Segala = S (KD (K Segala)) deriving (Eq, Show)

-- | Datatype for propositional clauses
data Clause a = Implies [a] [a] deriving (Eq, Ord, Show)
-- | Datatype for substitutions
data Subst a = Subst (Map.Map Int a) deriving (Eq, Show)

-- | Logic Class
class Logic a b | a -> b, b -> a where
  match :: Clause (a c) -> [(b, Subst (Boole c))]
  clauses :: b -> [Clause Int]
  subclauses :: Ord c => Clause (a c) -> [Clause (a c)]

-- | Logic instance for K modal logic
instance Logic K RK where
  match ((Implies n p)::Clause (K c)) = 
    let i = length n; cStrip (K x) = x
        substHead = (i+1,cStrip(head p))
        substTail = zip [1..i] (map cStrip n)
    in [(RK i, Subst (Map.fromList (substHead:substTail)))]
  clauses (RK n) = [Implies [1..n] [n+1]]
  subclauses (Implies n p) = [Implies n [l] | l <- p]
-- | Logic instance for KD modal logic
instance Logic KD RKD where
  match ((Implies n p):: Clause (KD c)) = 
    let i = length n; cStrip (KD x) = x
        substHead = (i+1,cStrip(head p))
        substTail = zip [1..i] (map cStrip n)
    in [(RKDPos i, Subst (Map.fromList (substHead:substTail)))]
  clauses (RKDPos n) = case n of
                        0 -> [Implies [] [1]]
                        _ -> [Implies [1..n] [n+1]]
  clauses (RKDNeg n) = [Implies [1..n] []]
  subclauses (Implies n p) = [Implies n [l] | l <- p]

