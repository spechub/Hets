{- | Module     : $Header$
 -  Description : Implementation of logic instance Graded Modal Logic
 -  Copyright   : (c) Daniel Hausmann & Georgel Calin & Lutz Schroeder, DFKI Lab Bremen,
 -                Rob Myers & Dirk Pattinson, Department of Computing, ICL 
 -  License     : GPLv2 or higher
 -  Maintainer  : hausmann@dfki.de
 -  Stability   : provisional
 -  Portability : portable
 -
 - Provides the implementation of the matching functions of graded modal logic.
 -}

module GMP.Logics.G where
import List
import Ratio
import Maybe

import Debug.Trace
import Text.ParserCombinators.Parsec

import GMP.Logics.Generic
import GMP.Parser
import GMP.Logics.IneqSolver

--------------------------------------------------------------------------------
-- instance of feature for graded modal logic
--------------------------------------------------------------------------------

data G a = G Int [Formula a] deriving (Eq,Show)	

instance (SigFeature b c d, Eq (b (c d)), Eq (c d)) => NonEmptyFeature G b c d where
    nefMatch flags seq = let poslits = keep_poslits seq
                             neglits = keep_neglits seq
                             -- take all combinations of positive and negative modal literals
                             all_combinations = [ (pos,neg) |
                                   pos <- (powerList poslits), neg <- (powerList neglits)] \\ [([],[]) ]
                             multiplicities xs = map (\(Mod (G k _)) -> k) xs
                             strip_neg (Neg phi) = phi
                             side_condition_tuples (p,n) = 
                               let switch l = map (\(x,y)->(y,map negate x)) l
                               in switch $ ineqSolver (Coeffs (map (1+) (multiplicities (map strip_neg n))) (multiplicities p))
                                                      (gml_bound ((multiplicities p),(multiplicities (map strip_neg n))))
                             gml_match (ps,ns) = map (gml_build_matches (ps,ns))
                                                     (gml_filter_tuples (side_condition_tuples (ps,ns)) [] )
                         in map gml_match all_combinations
    nefPretty d = case d of 
                    G i [] -> "[G]" ++ show i ++ "empty,mann"
                    G i e -> "[G]" ++ show i ++ (pretty (head e))
    nefFeatureFromSignature sig = G 1
    nefFeatureFromFormula phi = G 1
    nefStripFeature (G i phis) = phis

    nefDisj2Conj (Mod (G i phi)) = Mod (G i ([disj2conj (head phi)]))
    nefNegNorm (Mod (G i phi)) = Mod (G i ([negNorm (head phi)]))

    nefParser sig = do n <- natural
                       return $ G (fromInteger n)

--------------------------------------------------------------------------------
-- additional functions for the matching function of this logic
--------------------------------------------------------------------------------

gml_build_matches :: (SigFeature a b c, Eq (a (b c))) => ([Formula (G (a (b c)))],[Formula (G (a (b c)))]) -> ([Int],[Int]) -> [Sequent]
gml_build_matches (poslits,neglits) (prs,nrs) =
 	      let (pos_inds,neg_inds) = (to_inds prs,to_inds nrs)
		  all_inds = [(pos,neg) | pos <- (powerList pos_inds), neg <- (powerList neg_inds)]
	 	  (sposlits,sneglits) = ([phi | Mod (G k [phi]) <- poslits],[phi | Neg (Mod (G k [phi])) <- neglits])
		  relevant_inds = filter (\(pos,neg) -> (sum $ imgInt pos prs) < (sum $ imgInt neg nrs)) all_inds
              in [Sequent (map (\(ps,ns) -> (Neg (andify (((map nneg ((img (pos_inds \\ ps) sposlits) ++ (img (neg_inds \\ ns) sneglits))) ++ ((img ps sposlits) ++ (img ns sneglits)))))) ) relevant_inds)]

-- GML bound on integer magnitude
gml_bound :: ([Int],[Int]) -> Int
gml_bound (kps,kns) = 
	let	n = (length kps) + (length kns)
		logint k x = ceiling $ logBase 2 (k + x)
		logsum ls k = sum $ map (\x -> logint k (fromIntegral(x))) ls	
	in	12*n*(1+n) + 6*n*((logsum kps 1) + (logsum kns 2))

gml_filter_tuples :: [([Int], [Int])] -> [([Int], [Int])] -> [([Int], [Int])]
gml_filter_tuples [] bs = bs
gml_filter_tuples (a:as) bs
      | any (\x -> gml_geq x a) bs = gml_filter_tuples as bs
      | otherwise = a:(filter (\x -> not (gml_leq x a)) bs)

gml_leq ::  ([Int],[Int]) ->  ([Int],[Int]) -> Bool
gml_leq (p1, n1) (p2, n2) =  (and (( map (\(x, y) -> x <= y) (( zip p1 p2) ++ (zip  n1 n2)))))

gml_geq ::  ([Int],[Int]) ->  ([Int],[Int]) -> Bool
gml_geq (p1, n1) (p2, n2) =  (and (( map (\(x, y) -> x >= y) (( zip p1 p2) ++ (zip  n1 n2)))))

--------------------------------------------------------------------------------
-- instance of sigFeature for graded modal logic
--------------------------------------------------------------------------------

instance (SigFeature b c d, Eq (c d), Eq (b (c d))) => NonEmptySigFeature G b c d where
  neGoOn sig flag = genericPGoOn sig flag

