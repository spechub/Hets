{- | Module     : $Header$
 -  Description : Implementation of logic instance Probabilistic modal logic
 -  Copyright   : (c) Daniel Hausmann & Georgel Calin & Lutz Schroeder, DFKI Lab Bremen,
 -                Rob Myers & Dirk Pattinson, Department of Computing, ICL 
 -  License     : GPLv2 or higher, see LICENSE.txt
 -  Maintainer  : hausmann@dfki.de
 -  Stability   : provisional
 -  Portability : portable
 -
 - Provides the implementation of the matching functions of probabilistic modal logic.
 -}

module GMP.Logics.P where
import List
import Ratio
import Maybe

import Debug.Trace
import Text.ParserCombinators.Parsec

import GMP.Logics.Generic
import GMP.Parser

--------------------------------------------------------------------------------
-- instance of Probabilistic Modal Logic and needed functions
--------------------------------------------------------------------------------

data P a = P Rational [Formula a] deriving (Eq,Show)

instance (SigFeature b c d, Eq (b (c d)), Eq (c d)) => NonEmptyFeature P b c d where
    nefMatch flags seq = let poslits = keep_poslits seq
                             neglits = keep_neglits seq
                             -- take all combinations of positive and negative modal operators
                             all_combinations = [ (pos, neg) | pos <- map nub (powerList poslits),
                                                               neg <- map nub (powerList neglits)] \\ [([],[])]
                             probabilities xs = map (\(Mod (P k _)) -> k) xs
                             strip_neg (Neg phi) = phi
                             bound (p,n) = pml_bound ((probabilities p),(probabilities (map strip_neg n)))
  	                     tuples (p,n) = nub [(pts,nts,k)| pts <- (tuprange (bound (p,n)) (length p)),  
	 	                                              nts <- (tuprange (bound (p,n)) (length n)),
		                                              k <- [-(bound (p,n))..(bound (p,n))]]
                             side_condition_tuples (p,n) = filter (pml_side_condition (p,n)) (tuples (p,n))
                             pml_match (p,n) = -- trace ("\n  filtered tuples:" 
                                               --        ++ show((pml_filter_tuples (side_condition_tuples (p,n)) []))) $
                                                  map (pml_build_matches (p,n)) 
                                                      (pml_filter_tuples (side_condition_tuples (p,n)) [])
                         in if (flags!!1)
                              then 
                                trace ("\n  allc: tracing defunct" )
                                map pml_match all_combinations
                              else map pml_match all_combinations

    nefPretty d = case d of 
                    P r [] -> "[P]" ++ show r ++ "empty,mann"
                    P r e -> "[P]" ++ show r ++ (pretty (head e))
    nefFeatureFromSignature sig = P 1
    nefFeatureFromFormula phi = P 1
    nefStripFeature (P i phis) = phis

    nefDisj2Conj (Mod (P r phi)) = Mod (P r ([disj2conj (head phi)]))
    nefNegNorm (Mod (P r phi)) = Mod (P r ([negNorm (head phi)]))

    nefParser sig = 
     do x <- natural
        let auxP n =  do char '/'
                         m<-natural
                         return $ toRational (fromInteger n/fromInteger m)
                  <|> do char '.'
                         m<-natural
                         let noDig n
                               | n<10 = 1
                               | n>=10 = 1 + noDig (div n 10)
                         let rat n = toRational(fromInteger n / 
                                                fromInteger (10^(noDig n)))
                         let res = toRational n + rat m
                         return res
                  <|> do return $ toRational n
                  <?> "Parser.parsePindex.auxP"
        aux <- auxP x
        return $ P aux

--------------------------------------------------------------------------------
-- additional functions for the matching function of this logic
--------------------------------------------------------------------------------

pml_build_matches :: (SigFeature a b c, Eq (a (b c))) => ([Formula (P (a (b c)))],[Formula (P (a (b c)))]) -> ([Int],[Int],Int) -> [Sequent]
pml_build_matches (poslits,neglits) (prs,nrs,k) =
	let	(pos_inds,neg_inds) = (to_inds prs,to_inds nrs)
		all_inds = [(pos,neg) | pos <- (powerList pos_inds), neg <- (powerList neg_inds)]
	 	(sposlits,sneglits) = ([phi | Mod (P k [phi]) <- poslits],[phi | Neg (Mod (P k [phi])) <- neglits])
                relevant_inds = filter (\(pos,neg) -> (sum $ imgInt pos prs) - (sum $ imgInt neg nrs) < k)
                                       all_inds
		getJ (ps,ns) = (img ps sposlits) ++
                               (img ns sneglits)
		getnJ (ps,ns) = (img (pos_inds \\ ps) sposlits) ++
                                (img (neg_inds \\ ns) sneglits)
        in [Sequent (map (\rs -> Neg (andify ((map nneg (getnJ rs)) ++ (getJ rs))) )
                      relevant_inds)]

pml_side_condition :: ([Formula (P (a (b c)))],[Formula (P (a (b c)))]) -> ([Int],[Int],Int) -> Bool
pml_side_condition (pls,nls) (pints,nints,k) =
	let	(rpints,rnints) = (map fromIntegral pints,map fromIntegral nints)
		psum = sum $ zipbin (*) rpints (map (\(Mod(P x _))->fromRational(x)) pls)
		nsum = sum $ zipbin (*) rnints (map (\(Neg(Mod(P x _)))-> fromRational(-x)) nls)
	in	if null(pints) 	then (psum + nsum < fromIntegral(k))
						else (psum + nsum <= fromIntegral(k))

pml_bound :: ([Rational],[Rational]) -> Int
pml_bound (rps,rns) = 
	let	n = (length rps) + (length rns)
		toints rs = concatMap (\r -> [numerator r,denominator r]) rs
		allints = (toints rps) ++ (toints rns)
		logint x = ceiling(logBase 2 (1 + x))
		logsum = sum $ map (\y -> logint (fromIntegral(y))) allints
	in	20*n*n*(1+n) + 10*n*n*logsum

-- find maximal elts of those tuples satisfying the side condition
pml_filter_tuples :: [([Int], [Int], Int)] -> [([Int], [Int], Int)] -> [([Int], [Int], Int)]
pml_filter_tuples [] bs = bs
pml_filter_tuples (a:as) bs
		 | any (\x -> pml_geq x a) bs = pml_filter_tuples as bs
		 | otherwise = a:(filter (\x -> not (pml_leq x a)) bs)

pml_leq ::  ([Int],[Int], Int) ->  ([Int],[Int], Int) -> Bool
pml_leq (p1, n1, k1) (p2, n2, k2) = (k1 == k2) &&
                                    (and (( map (\(x, y) -> x <= y) ((zip p1 p2) ++
                                                                     (zip n1 n2)))))

pml_geq ::  ([Int],[Int], Int) ->  ([Int],[Int], Int) -> Bool
pml_geq (p1, n1, k1) (p2, n2, k2) = (k1 == k2) &&
                                    (and (( map (\(x, y) -> x >= y) ((zip p1 p2) ++
                                                                     (zip n1 n2)))))

-- Construct all integer n-tuples with elements from 1,..,r
tuprange :: Int -> Int -> [[Int]]
tuprange _ 0 = [[]]
tuprange r n = 
	let rec xs ys = map (\z -> z:ys) xs
	in	concatMap (rec [1..r]) (tuprange r (n-1))

-- zip two lists together using a binary operator
zipbin :: (a -> a -> a) -> [a] -> [a] -> [a]
zipbin _ [] _ = [];	zipbin _ _ [] = [];
zipbin f (x:xs) (y:ys) = (f x y):(zipbin f xs ys)

--------------------------------------------------------------------------------
-- instance of sigFeature for probabilistic modal logic
--------------------------------------------------------------------------------

instance (SigFeature b c d, Eq (c d), Eq (b (c d))) => NonEmptySigFeature P b c d where
  neGoOn sig flag = genericPGoOn sig flag
