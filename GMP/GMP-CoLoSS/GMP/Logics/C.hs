{- | Module     : ./GMP/GMP-CoLoSS/GMP/Logics/C.hs
 -  Description : Implementation of logic instance Coalition Logic
 -  Copyright   : (c) Daniel Hausmann & Georgel Calin & Lutz Schroeder, DFKI Lab Bremen,
 -                Rob Myers & Dirk Pattinson, Department of Computing, ICL
 -  License     : GPLv2 or higher, see LICENSE.txt
 -  Maintainer  : hausmann@dfki.de
 -  Stability   : provisional
 -  Portability : portable
 -
 - Provides the implementation of the matching functions of coalition logic.
 -}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FlexibleContexts #-}
module GMP.Logics.C where
import Data.List
import Data.Ratio
import Data.Maybe

import Debug.Trace
import Text.ParserCombinators.Parsec

import GMP.Logics.Generic
import GMP.Parser

{- ------------------------------------------------------------------------------
instance of feature for coalition logic
------------------------------------------------------------------------------ -}

data C a = C [Int] [Formula a] deriving (Eq, Show)

agents :: Int; agents = 10

{- For each positive modal literal, there are possibly serveral premises,
containing only one sequent each. This sequent contains the stripped positive
literal and additional stripped literals which are computed by
'c_build_matches'. Also there is one additional premise, containing the sequent
of all negated stripped negative literals.
e.g. seq       = [ (M (C [0,3]) p), !(M (C [0]) q), (M (C [0,2,3]) !p), !(M (C [1]) !r)]
match seq = [ [[ p, !p, !q ]], [[ p, !p, !q]], [[!q, r]] ] -}
instance (SigFeature b c d, Eq (b (c d)), Eq (c d)) => NonEmptyFeature C b c d where
    nefMatch flags seq = let neglits = [ Neg phi | Neg (Mod (C s [phi])) <- seq ]
                             poslits = [ phi | Mod (C s [phi]) <- seq ]
                         in [ [[Sequent (c_match ++ poslits)]] |
                              c_match <- c_build_matches (keep_poslits seq)
                              (keep_neglits seq)] ++ [[[Sequent neglits]]]
    nefPretty d = case d of
                    C l [] -> "[C]" ++ show l ++ "nothing contained"
                    C l e -> "[C]" ++ show l ++ pretty (head e)
    nefFeatureFromSignature sig = C [1]
    nefFeatureFromFormula phi = C [1]
    nefStripFeature (C i phis) = phis

    nefDisj2Conj (Mod (C l phi)) = Mod (C l [disj2conj (head phi)])
    nefNegNorm (Mod (C l phi)) = Mod (C l [negNorm (head phi)])

    nefParser sig = do -- checks whether there are more numbers to be parsed
                      let stopParser =  do char ','
                                           return False
                                    <|> do char '}'
                                           return True
                                    <?> "Parser.parseCindex.stop"
                      -- checks whether the index is of the form x1,..,x&
                      let normalParser l =  do x <- natural
                                               let n = fromInteger x
                                               spaces
                                               q <- stopParser
                                               spaces
                                               if q then normalParser (n : l)
                                                 else return (n : l)
                                        <?> "Parser.parseCindex.normal"
                      char '{'
                      res <- try (normalParser [])
                      return $ C res
               <|> do -- checks whether the index is of the form "n..m"
                      let shortParser =  do x <- natural
                                            let n = fromInteger x
                                            spaces
                                            string ".."
                                            spaces
                                            y <- natural
                                            let m = fromInteger y
                                            return [n .. m]
                                     <?> "Parser.parseCindex.short"
                      res <- try shortParser
                      return $ C res
               <?> "Parser.parseCindex"

{- ------------------------------------------------------------------------------
additional functions for the matching function of this logic
------------------------------------------------------------------------------ -}

-- Form negative literal parts of matching premise for positive literals
c_build_matches :: (Eq b) => [Formula (C b)] -> [Formula (C b)] -> [[Formula b]]
c_build_matches [] _ = []
c_build_matches ( Mod (C pset pphi) : pls) nls =
        let relevant_neglits = filter (\ (Neg (Mod (C s _))) -> ((s `intersect` pset) == s)) nls
            relevant_ncoalitions = nub $ map (\ (Neg (Mod (C s _))) -> s) relevant_neglits
            maximal_pw_dis_lists = rm_sublists $ sortBy compare_length
                                    (filter pairwise_disjunct
                                           (powerList relevant_ncoalitions))
            negmats = [ [Neg phi] | [Neg (Mod (C s [phi]))] <-
             concatMap (build_lit_lists relevant_neglits) maximal_pw_dis_lists]
        in map ([head pphi] ++) negmats ++ c_build_matches pls nls

{- Given a list of negative literals and a list of pairwise disjunctive lists, form pairwise
disjunctive lists of the according literals -}
build_lit_lists :: (Eq b) => [Formula (C b)] -> [[Int]] -> [[Formula (C b)]]
build_lit_lists _ [] = [[]]
build_lit_lists lits (set : sets) =
  let relevant_neglits = filter (\ (Neg (Mod (C t _))) -> set == t) lits
  in if null relevant_neglits then [] else
     map ([head relevant_neglits] ++) (build_lit_lists lits sets)
      ++ build_lit_lists (lits \\ [head relevant_neglits]) (set : sets)

-- Does the list contain only pairwise disjunct lists?
pairwise_disjunct :: (Eq a) => [[a]] -> Bool
pairwise_disjunct [] = True
pairwise_disjunct (x : xs) = all (\ y -> null (x `intersect` y)) xs &&
                             pairwise_disjunct xs

-- Remove sublists (i.e. keep only maximal lists). Requires input to be sorted
rm_sublists :: (Eq a) => [[a]] -> [[a]]
rm_sublists [] = []
rm_sublists (x : xs) | any (\ y -> x `intersect` y == x) xs = rm_sublists xs
                     | otherwise = x : rm_sublists xs

-- Compare lists by size.
compare_length :: [a] -> [a] -> Ordering
compare_length s t = if length s < length t then LT else GT

{- ------------------------------------------------------------------------------
instance of sigFeature for coalition logic
------------------------------------------------------------------------------ -}

instance (SigFeature b c d, Eq (c d), Eq (b (c d))) => NonEmptySigFeature C b c d where
  neGoOn = genericPGoOn
