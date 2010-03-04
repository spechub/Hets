{- | Module     : $Header$
 -  Description : Implementation of logic instance CK+CEM
 -  Copyright   : (c) Daniel Hausmann & Georgel Calin & Lutz Schroeder, DFKI Lab Bremen,
 -                Rob Myers & Dirk Pattinson, Department of Computing, ICL 
 -  License     : Similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
 -  Maintainer  : hausmann@dfki.de
 -  Stability   : provisional
 -  Portability : portable
 -
 - Provides the implementation of the matching functions of conditional logic plus
 - conditional excluded middle.
 -}

module GMP.Logics.Con where
import List
import Ratio
import Maybe

import Debug.Trace
import Text.ParserCombinators.Parsec

import GMP.Logics.Generic
import GMP.Parser

--------------------------------------------------------------------------------
-- instance of feature for CK+CEM
--------------------------------------------------------------------------------

data Con a = Con [Formula a] deriving (Eq,Show)	

instance (SigFeature b c d, Eq (b (c d)), Eq (c d)) => NonEmptyFeature Con b c d where
-- For any set of logically equivalent premises A1,...,An, there are two premises:
-- The first premise contains the (negated) stripped conclusions of (negative)
-- literals with a premise from A1,...,An.
-- The second premise contains just the statement that all A1,...,An are
-- logically equivalent.
  nefMatch flags seq = let neglits premises = [ (Neg phi) | (Neg(Mod (Con (psi:phi:_)))) <- seq, psi `elem` premises]
                           poslits premises = [ phi | (Mod (Con (psi:phi:_))) <- seq, psi `elem` premises]
                       in if (flags!!1)
                            then 
                              [ trace ("  <Trying to match... Current antecedents:>     ["
                                       ++ (pretty_list prems) ++ "]") $
                                [[Sequent (are_equiv prems)]] ++
                                [[Sequent ((neglits prems) ++ (poslits prems))]]
                                 | prems <- (power_premises seq)]
                            else
                              [ [[Sequent (are_equiv prems)]] ++
                                [[Sequent ((neglits prems) ++ (poslits prems))]]
                                 | prems <- (power_premises seq)]

  nefPretty d = genfPretty d "[Con]"
  nefFeatureFromSignature sig = Con
  nefFeatureFromFormula phi = Con
  nefStripFeature (Con phis) = phis
  nefSeparator sig = "=>"

--------------------------------------------------------------------------------
-- additional functions for the matching function of this logic
--------------------------------------------------------------------------------

-- create sequent which states that all elements of the input list are equivalent
-- to the input formula.
are_equiv :: (Feature a b) => [Formula (a b)] -> [Formula (a b)]
are_equiv [] = []
are_equiv (psi:[]) = -- trace ("  <Identity not needed to prove:>               " 
                     --        ++ (pretty psi) ++ " = " ++ (pretty psi)) $ 
                     []
are_equiv (psi:phi:xs) =  -- trace ("  <One pair to prove:>                          "
                          --        ++ (pretty phi) ++ " = " ++ (pretty psi)) $ 
                          (And (Neg (And (Neg psi) phi)) (Neg (And (Neg phi) psi))) :
                          (are_equiv (psi:xs))

-- return the premises of each positive or negative literal in the input sequent
con_premises :: (Feature Con b) => [Formula (Con b)] -> [Formula b]
con_premises seq = [psi | (Mod (Con (psi:phi:_))) <- seq] ++
                   [psi | (Neg (Mod (Con (psi:phi:_)))) <- seq]

-- return the list of all combinations of premises that appear in the input
-- sequent
power_premises :: (Feature Con b) => [Formula (Con b)] -> [[Formula b]]
power_premises xs = powerList (con_premises xs)

--------------------------------------------------------------------------------
-- instance of sigFeature for Conditional logic with conditional excluded middle
--------------------------------------------------------------------------------

instance (SigFeature b c d, Eq (c d), Eq (b (c d))) => NonEmptySigFeature Con b c d where
  neGoOn sig flag = genericPGoOn sig flag

