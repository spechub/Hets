{- | Module     : $Header$
 -  Description : Implementation of generic data structures and functions
 -  Copyright   : (c) Daniel Hausmann & Georgel Calin & Lutz Schroeder, DFKI Lab Bremen,
 -                Rob Myers & Dirk Pattinson, Department of Computing, ICL 
 -  License     : Similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
 -  Maintainer  : hausmann@dfki.de
 -  Stability   : provisional
 -  Portability : portable
 -
 - Provides the implementation of the generic algorithm for checking 
 - satisfiability/provability of several types of modal logics.
 -}
module GMP.Logics.Generic where

import List
import Ratio
import Maybe
import Text.ParserCombinators.Parsec
import Debug.Trace
import Control.Monad.ST

--------------------------------------------------------------------------------
-- basic data types
--------------------------------------------------------------------------------

-- Formulae
data Formula a = F | T | And (Formula a) (Formula a) | Or (Formula a) (Formula a) | 
     	      Neg (Formula a) | Atom Int | Mod a deriving (Eq, Ord, Show)

--------------------------------------------------------------------------------
-- List of (possibly heterogenous) premises:
-- a list of premises may contain sequents with different types...
--------------------------------------------------------------------------------

-- A sequent is a list of formulae
data Sequent = forall a b c. (Feature a (b c), Eq (a (b c))) => Sequent [Formula (a (b c))]

-- A list of premises is a list of a list of sequent
type Premises = [[[Sequent]]]

data ModalOperator = Sqr | Ang | None
    deriving Eq

--------------------------------------------------------------------------------
-- feature type-class
-- the feature type-class carries the matching function...
--------------------------------------------------------------------------------

class Feature a b where
-- basic methods
  fMatch :: [Bool] -> [Formula (a b)] -> Premises 
  fPretty :: (a b) -> String
  fFeatureFromSignature :: (a b) -> [Formula e] -> a e
  fFeatureFromFormula :: Formula (a b) -> [Formula e] -> a e
  fStripFeature :: (a b) -> [Formula b]

  fDisj2Conj :: Formula (a b) -> Formula (a b)
  fNegNorm :: Formula (a b) -> Formula (a b)
  fStripFormula :: Formula (a b) -> (a b)
  fStripFormula phi = case phi of
                        T -> (fFeatureFromFormula phi) []
                        F -> (fFeatureFromFormula phi) []
                        (And psi xi) -> (fStripFormula psi)
                        (Or psi xi) -> (fStripFormula psi)
                        (Neg psi) -> (fStripFormula psi)
                        (Mod sig) -> sig
-- parsing methods
  fNext :: (a b) -> b
  fParser :: (a b) -> Parser ([Formula e] -> a e)
  fSeparator :: (a b) -> String
-- preproving methods
  fDepth :: (a b) -> Int
  fPreProve :: [Formula (a b)] -> Int -> [[Formula (a b)]] -> [[Formula (a b)]]
  fPreProve seq i ecs = []
  fMatchOptimised :: [Bool] -> [Formula (a b)] -> [[Formula (a b)]] -> Premises 
  fMatchOptimised flags seq ecs = fMatch flags seq

-- state monad stuff
  fGetCache :: (a b) -> [Formula (a b)]
  fGetCache sig = fst $ (runState get [])
  fPutCache :: (a b) -> [Formula (a b)] -> (GMPState [Formula (a b)]) ()
  fPutCache sig s = put s

newtype GMPState s a = GMPState { runState :: (s -> (a,s)) } 
 
instance Monad (GMPState s) where 
    return a           = GMPState $ \s -> (a,s)
    (GMPState x) >>= f = GMPState $ \s -> let (v,s') = x s in runState (f v) s' 

class MonadState m s | m -> s where 
    get :: m s
    put :: s -> m ()

instance MonadState (GMPState s) s where 
    get   = GMPState $ \s -> (s,s) 
    put s = GMPState $ \_ -> ((),s) 

--------------------------------------------------------------------------------
-- nonempty-features are a subclass of features
-- they have more default-functions than normal features though
--------------------------------------------------------------------------------

class (SigFeature b c d, Eq (c d)) => NonEmptyFeature a b c d where
  nefMatch :: [Bool] -> [Formula (a (b (c d)))] -> Premises 
  nefPretty :: (a (b (c d))) -> String
  nefFeatureFromSignature :: (a (b (c d))) -> [Formula e] -> a e
  nefFeatureFromFormula :: Formula (a (b (c d))) -> [Formula e] -> a e
  nefStripFeature :: (a (b (c d))) -> [Formula (b (c d))]
  nefDisj2Conj :: Formula (a (b (c d))) -> Formula (a (b (c d)))
  nefDisj2Conj = genfDisj2Conj
  nefNegNorm :: Formula (a (b (c d))) -> Formula (a (b (c d)))
  nefNegNorm = genfNegNorm
  nefNext :: (a (b (c d))) -> (b (c d))
  nefNext sig = genfNext sig
  nefDepth :: (a (b (c d))) -> Int
  nefDepth = genfDepth 
  nefParser :: (a (b (c d))) -> Parser ([Formula e] -> a e)
  nefParser sig = return (nefFeatureFromSignature sig)
  nefSeparator :: (a (b (c d))) -> String
  nefSeparator sig = ","

instance (NonEmptyFeature a b c d, Eq (c d)) => Feature a (b (c d)) where
  fMatch = nefMatch
  fDisj2Conj = nefDisj2Conj
  fNegNorm = nefNegNorm
  fDepth = nefDepth
  fNext = nefNext
  fPretty = nefPretty
  fFeatureFromSignature = nefFeatureFromSignature
  fFeatureFromFormula = nefFeatureFromFormula
  fStripFeature = nefStripFeature
  fParser = nefParser
  fSeparator = nefSeparator

--------------------------------------------------------------------------------
-- sigfeature type-class
-- the sigfeature type-class ensures correct order of features...
--------------------------------------------------------------------------------

class (Feature a (b c), Feature b c, Eq c) => SigFeature a b c where
-- basic methods
  sMatch :: (Eq c) => [Bool] -> [Formula (a (b c))] -> Premises 
  sDisj2Conj :: Formula (a (b c)) -> Formula (a (b c))
  sNegNorm :: Formula (a (b c)) -> Formula (a (b c))
  sPretty :: (a (b c)) -> String
-- parsing methods
  sParser :: (a (b c)) -> Parser ([Formula e] -> a e)
  sParser = fParser
  sNextSig :: (a (b c)) -> (b c)
  sNextSig = fNext
  pGoOn :: (a (b c)) -> ModalOperator ->  Parser (Formula (b c))
-- preproving methods
  sDepth :: Formula (a (b c)) -> Int

--------------------------------------------------------------------------------
-- nonempty-sigfeatures are a subclass of sigfeatures
-- they have more default-functions than normal sigfeatures though
--------------------------------------------------------------------------------

class (SigFeature b c d, Eq d, Feature a (b (c d)), Feature b (c d), Eq (c d)) => NonEmptySigFeature a b c d where
  neMatch :: (Eq (c d)) => [Bool] -> [Formula (a (b (c d)))] -> Premises 
  neMatch = fMatch
  neGoOn :: (a (b (c d))) -> ModalOperator ->  Parser (Formula (b (c d)))
  neDisj2Conj :: Formula (a (b (c d))) -> Formula (a (b (c d)))
  neDisj2Conj = fDisj2Conj
  neNegNorm :: Formula (a (b (c d))) -> Formula (a (b (c d)))
  neNegNorm = fNegNorm
  neDepth :: Formula (a (b (c d))) -> Int
  neDepth = genSDepth
  nePretty :: (a (b (c d))) -> String
  nePretty sig = "{NonEmpty} " ++ fPretty sig

instance (NonEmptySigFeature a b c d, Eq (c d)) => SigFeature a b (c d) where
  sMatch = neMatch
  pGoOn = neGoOn
  sDisj2Conj = neDisj2Conj
  sNegNorm = neNegNorm
  sDepth = neDepth
  sPretty = nePretty


--------------------------------------------------------------------------------
-- Generic functions for Features
--------------------------------------------------------------------------------

genfDepth :: (Feature a (b (c d)), SigFeature b c d) => (a (b (c d))) -> Int
genfDepth sig = case (fStripFeature sig) of
                  [phi] -> sDepth phi

genfNext :: (Feature a (b (c d)), SigFeature b c d) => (a (b (c d))) -> (b (c d))
genfNext sig = case fStripFeature sig of 
                      []   -> fStripFormula (F)
                      phis -> fStripFormula (head phis)

genfDisj2Conj :: (Feature a (b (c d)), SigFeature b c d) => Formula (a (b (c d))) -> Formula (a (b (c d)))
genfDisj2Conj phi = Mod ((fFeatureFromFormula phi) (map disj2conj (fStripFeature (fStripFormula phi))))

genfNegNorm :: (Feature a (b (c d)), SigFeature b c d) => Formula (a (b (c d))) -> Formula (a (b (c d)))
genfNegNorm phi = Mod ((fFeatureFromFormula phi) (map negNorm (fStripFeature (fStripFormula phi))))

genfPretty :: (Feature a (b (c d)), SigFeature b c d) => a (b (c d)) -> String -> String
genfPretty d s = case fStripFeature d of 
                    []     -> s ++ " nothing contained!"
                    (e:[]) -> s ++ (pretty e)
                    e      -> s ++ show (map pretty e)

--------------------------------------------------------------------------------
-- Generic functions for SigFeatures
--------------------------------------------------------------------------------

-- generic matching for sigfeatures (uses matching function of underlaying feature)
genSMatch :: (SigFeature a b (c d), SigFeature b c d, Eq d) => [Bool] -> [Formula (a (b (c d)))] -> Premises
genSMatch flags seq = fMatch flags seq

-- the depth of modal nesting of a list of formulae
ldepth :: (SigFeature a b c) => [Formula (a (b c))] -> Int
ldepth seq = maximum (map genSDepth seq)

-- generic depth of modal nesting of a formula
genSDepth :: (SigFeature a b c) => Formula (a (b c)) -> Int
genSDepth F = 0
genSDepth T = 0
genSDepth (Atom i) = 0
genSDepth (Neg phi) = genSDepth (phi)
genSDepth (And phi psi) = max (genSDepth phi) (genSDepth psi)
genSDepth (Or phi psi) = max (genSDepth phi) (genSDepth psi)
genSDepth (Mod xs) = 1 + (fDepth xs)

-- generic function to return all top-level modal arguments of phi
--genSGetArgs :: (SigFeature a, Feature b, Eq e) => Formula (a (b (c (d e)))) -> [Formula (c (d e))]
--genSGetArgs phi = case phi of 
--                         T -> []
--                         F -> []
--                         (Atom i) -> []
--                         (Neg psi) -> sGetArgs psi
--                         (And xi yi) -> sGetArgs xi ++ sGetArgs yi
--                         (Or xi yi) -> sGetArgs xi ++ sGetArgs yi
--                         (Mod sig) -> fStripFeat (sNextSig sig)

-- generic function to return all top-level modal arguments of phi
--genHGetArgs :: (SigFeature a, Feature b, Eq e) => Formula (a (b (c (d e)))) -> [Formula (c (d e))] :*: HNil
--genHGetArgs phi = case phi of 
--                         T -> [] .*. HNil
--                         F -> [] .*. HNil
--                         (Atom i) -> [] .*. HNil
--                         (Neg psi) -> hGetArgs psi
--                         (And xi yi) -> (hHead (hGetArgs xi) ++ hHead (hGetArgs yi)) .*. HNil
--                         (Or xi yi) -> (hHead (hGetArgs xi) ++ hHead (hGetArgs yi)) .*. HNil
--                         (Mod sig) -> fStripFeat (sNextSig sig) .*. HNil

-- generic function to return the list of all arguments of modality that
-- have nesting depth at most i
--genSGetPrems :: (SigFeature a, Feature b, SigFeature c, Feature d, Eq e) =>
--                 Int -> Formula (a (b (c (d e)))) -> [Sequent]
--genSGetPrems i phi = if (sDepth phi) <= i then
--                       let args = (sGetArgs phi)
--                       in (Sequent args) : concatMap (sGetPrems i) (args)
--                     else
--                       let args = (sGetArgs phi)
--                       in concatMap (sGetPrems i) (args)

--------------------------------------------------------------------------------
-- generic functions for preproving
--------------------------------------------------------------------------------

-- given a formula, a number i(=0) and a list of classes, compute the list of
-- preproving classes for the formula.
--genSPreProve :: (SigFeature a, Feature b, SigFeature c, Feature d, Eq g) =>
--                   Formula (a (b (c (d (e (f g)))))) -> Int -> [[Sequent]] -> [[Sequent]]
--genSPreProve phi i seqs = let eq = (genClasses (merge (collapse (sGetPrems i phi)) seqs))
--                         in if (i == (sDepth phi)-1) then eq
--                                                     else eq ++ (genSPreProve phi (i+1) eq)

-- not done yet ([[1]:A, [2]:B, [3]:C, [4]:A] -> [[1,4]:A, [2]:B, [3:C]]): 
--collapse :: [Sequent] -> [Sequent]
--collapse ((Sequent phis):seqs) = (Sequent phis):seqs

-- not done yet ([[1]:ABC, [2]:CDE],[[[3]:ABC,[4]:ABC],[[5]:CDE,[6]:CDE]] -> [([1],[[3],[4]]):ABC, ([2],[[5],[6]]):CDE]):
--merge :: [Sequent] -> [[Sequent]] -> [DoubleSequent]
--merge [] [] = []

-- given a list of pairs of sequents of the same type (the pair consisting of
-- the formulas which are to be treated and a list of already known classes),
-- return the list of the list of classes for each pair.
--genClasses :: [DoubleSequent] -> [[Sequent]]
--genClasses [] = []
--genClasses (DoubleSequent (xis,eqs):seqs) = (classes (sFilter xis) eqs) : (genClasses seqs)

-- give preproving classes of a list list of formulas using the knowledge about
-- classes ppcs.
--classes :: (SigFeature a, Feature b, Eq e) => [Formula (a (b (c (d e))))] -> [[Formula (a (b (c (d e))))]] -> [Sequent]
--classes [] ppcs = []
--classes (phi:phis) ppcs = let ppc = nub (phi:(ppClass phi phis ppcs))
--                          in (Sequent ppc) : (classes ((phi:phis) \\ ppc) (ppc:ppcs))

-- given a formula phi and a list of formulae, return the list of all formulae
-- that are in the same class as phi (using the knowledge ppcs).
--ppClass :: (SigFeature a, Feature b, Eq e) => Formula (a (b (c (d e)))) -> [Formula (a (b (c (d e))))] ->
--                                        [[Formula (a (b (c (d e))))]] -> [Formula (a (b (c (d e))))]
--ppClass phi [] ppcs = []
--ppClass phi (psi:phis) ppcs = if (sCompute phi psi ppcs) then psi:(ppClass phi phis ppcs)
--                                                         else (ppClass phi phis ppcs)

-- check whether the two input formulae are equivalent. If they are already in
-- the same preproving class, it is not necessary to prove their equivalence.
--equiv :: (SigFeature a, Feature b, Eq e) => Formula (a (b (c (d e)))) -> Formula (a (b (c (d e)))) -> [[Formula (a (b (c (d e))))]] -> Bool
--equiv phi psi ppc = -- trace ("  <Trying to show equivalence:>                 " 
--                    --        ++ show (pretty phi) ++ " = " ++ show (pretty psi)) $ 
--                    (any (\eqcls -> ((phi `elem` eqcls) && (psi `elem` eqcls))) ppc) || 
--                    provable (And (Neg (And (Neg psi) phi)) (Neg (And (Neg phi) psi)))

--------------------------------------------------------------------------------
-- generic functions of (sig)features
--------------------------------------------------------------------------------

-- generic finishing feature
instance Feature a () where
  fMatch flags seq = trace "\n  <Matching not possible, no more layers>" $ [[]]
  fDisj2Conj phi = F
  fNegNorm phi = F
  fPretty e = " nothing contained!"
  fDepth phi = 0

-- generic finishing feature
instance Feature a (b ()) where
  fMatch flags seq = trace "\n  <Matching not possible, no more layers>" $ [[]]
  fDisj2Conj phi = F
  fNegNorm phi = F
  fPretty e = " nothing Contained!"
  fDepth phi = 0

-- generic finishing sigfeature
instance SigFeature a b () where
  sMatch flags seq = trace "\n  <Matching not possible, no more layers>" $ [[]]
  sDisj2Conj phi = F
  sNegNorm phi = F
  sPretty sig = "{Last SigFeature} " ++ fPretty sig
  sDepth phi = 0
  pGoOn sig flag = trace ("finishing: " ++ sPretty sig) $ return F

--------------------------------------------------------------------------------
-- preparsing functions
--------------------------------------------------------------------------------

-- | Preparsing replaces all disjunctions by conjunctions and normalizes negations -
-- | This is the form that the sequent calculus expects
preparse :: (SigFeature a b (c d), SigFeature b c d) => Formula (a (b (c d))) -> Formula (a (b (c d)))
preparse f = negNorm $ disj2conj f

disj2conj :: (SigFeature a b c) => Formula (a (b c)) -> Formula (a (b c))
disj2conj w = case w of
                      (And x y)   -> let a = disj2conj x
                                         b = disj2conj y
                                     in And a b
                      (Or x y)    -> let a = disj2conj x
                                         b = disj2conj y
                                     in Neg (And (Neg a) (Neg b))
                      (Neg x)     -> let a = disj2conj x
                                     in Neg a
                      (Mod phi)   -> sDisj2Conj (Mod phi)
                      x           -> x

negNorm :: (SigFeature a b c) => Formula (a (b c)) -> Formula (a (b c))
negNorm w = case w of
                    (Neg (Neg x)) -> negNorm x
                    (Neg x)       -> neg $ negNorm x
                    (Mod phi)     -> sNegNorm (Mod phi)
                    (And x y)     -> let a = negNorm x
                                         b = negNorm y
                                     in And a b
                    x             -> x -- there is no need for discussing "Or"


--------------------------------------------------------------------------------
-- some auxiliary functions which are used by several features
--------------------------------------------------------------------------------

-- generate the powerlist of a list
powerList :: [a] -> [[a]]
powerList [] = [[]]
powerList (x:xs) = powerList xs ++ (map (x:) (powerList xs))

-- Remove all formulas from a container that are not positive modal literals
keep_poslits :: [Formula (a b)] -> [Formula (a b)]
keep_poslits seq = filter (\phi -> case phi of (Mod _)->True;_->False) seq

-- Remove all formulas from a container that are not negative modal literals
keep_neglits :: [Formula (a b)] -> [Formula (a b)]
keep_neglits seq = filter (\phi -> case phi of (Neg(Mod _))->True;_->False) seq

-- Get list [0..(length xs)-1]
-- Needed for 'normal-forms' of G, P
to_inds :: [a] -> [Int]
to_inds [] = []
to_inds xs = [0..(length xs)-1]

-- Get the elements of a list that are indexed by the first parameter list
-- Needed for 'normal-forms' of G, P
img :: Eq (a (b c)) => [Int] -> [Formula (a (b c))] -> [Formula (a (b c))]
img inds xs = map (xs!!) inds 

imgInt :: [Int] -> [Int] -> [Int]
imgInt inds xs = map (xs!!) inds 

andify :: Eq (a (b c)) => [Formula (a (b c))] -> Formula (a (b c))
andify [] = F
andify (phi:[]) = phi
andify (phi:phis) = And phi (andify phis)

--------------------------------------------------------------------------------
-- remove empty sequents from a list of sequents
--------------------------------------------------------------------------------

emptifys :: [Sequent] -> [Sequent]
emptifys seqs = case seqs of
                  []               -> []
                  ((Sequent x):xs) -> case x of
                                         []   -> emptifys xs
                                         phis -> (Sequent x) : emptifys xs

emptifyss :: [[Sequent]] -> [[Sequent]]
emptifyss seqs = case seqs of
                  []     -> []
                  (x:xs) -> emptifys x : emptifyss xs

emptify :: Premises -> Premises
emptify prems = case prems of
                  []     -> []
                  (x:xs) -> emptifyss x : emptify xs

--------------------------------------------------------------------------------
-- basic sequent functions
--------------------------------------------------------------------------------

-- expand applies all sequent rules that do not branch
expand :: [Formula (a b)] -> [Formula (a b)]
expand [] = []
expand ((Neg (Neg phi)) : as) = expand (phi:as)
expand ((Neg (And phi psi)):as) = expand ((Neg phi):(Neg psi):as)
expand (a:as) = a:(expand as)

neg :: (SigFeature a b c) => Formula (a (b c)) -> Formula (a (b c))
neg psi = (Neg psi)

--------------------------------------------------------------------------------
-- pretty printing functions
--------------------------------------------------------------------------------

-- pretty print formula
pretty :: (Feature a (b c)) => Formula (a (b c)) -> String
pretty F = "F"; pretty T = "T";
pretty (Atom k) = "Atom" ++ (show k);
pretty (Or (Neg x) y) =  "(" ++ (pretty x) ++ ") --> (" ++ (pretty y) ++ ")"
pretty (Neg x) = "!" ++  (pretty x)
pretty (Or x y) = "(" ++ (pretty x) ++ ") OR (" ++ (pretty y) ++ ")"
pretty (And x y) = "(" ++ (pretty x) ++ ") AND (" ++ (pretty y) ++ ")"
pretty (Mod a) = (fPretty a)

-- pretty print sequent
pretty_seq :: Sequent -> String
pretty_seq (Sequent seq) = pretty_list seq

-- pretty print list of formulae
pretty_list :: (Feature a (b c)) => [Formula (a (b c))] -> String
pretty_list [] = "[]"
pretty_list (x:xs) = case xs of
                      [] -> pretty x
                      (y:ys) -> pretty x ++ " , " ++ pretty_list xs 

-- pretty print list of sequents
pretty_slist :: [Sequent] -> String
pretty_slist [] = ""
pretty_slist (x:xs) = case xs of
                      [] -> pretty_seq x
                      (y:ys) -> pretty_seq x ++ " , " ++ pretty_slist xs

-- pretty print a list of lists of sequents
prettyll :: [[Sequent]] -> String
prettyll [] = ""
prettyll (x:xs) = case x of
                     []     -> "[[]]"
                     (y:ys) -> case ys of
                                 [] -> "[" ++ pretty_seq y ++ "]" ++ prettyll xs
                                 (z:zs) -> "[" ++ pretty_seq y ++ "," ++ pretty_slist ys ++ "]" ++ prettyll xs

-- pretty print a list of lists of lists of sequents
prettylll :: [[[Sequent]]] -> String
prettylll [] = ""
prettylll (x:xs) = case x of
                      []     -> "[[]]"
                      (y:ys) -> case ys of
                                  [] -> "[" ++ pretty_slist y ++ "]" ++ prettylll xs
                                  (z:zs) -> "[" ++ pretty_slist y ++ "," ++ prettyll ys ++ "]" ++ prettylll xs

--------------------------------------------------------------------------------
-- 'polymorphic equality' type-class:
-- every feature is preserving the comparability of sequents...
--------------------------------------------------------------------------------

-- not needed?

--instance Eq a => Eq (b a)
--class PolyEq f
--  where g :: a -> f a
--instance Feature a b => PolyEq a
--instance (Eq a, PolyEq f) => Eq (f a)

--class Eq2 f
--class PolyEq2 f
--  where dzdu :: a -> f a
--instance SigFeature a b c => PolyEq2 a
--instance (Eq2 a, PolyEq2 f) => Eq2 (f a)
--instance Eq2 a => Eq a

