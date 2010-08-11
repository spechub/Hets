{- | Module     : $Header$
 -  Description : Implementation of generic data structures and functions
 -  Copyright   : (c) Daniel Hausmann & Georgel Calin & Lutz Schroeder, DFKI Lab Bremen,
 -                Rob Myers & Dirk Pattinson, Department of Computing, ICL 
 -  License     : GPLv2 or higher
 -  Maintainer  : hausmann@dfki.de
 -  Stability   : provisional
 -  Portability : portable
 -
 - Provides the implementation of the generic algorithm for checking 
 - satisfiability/provability of several types of modal logics.
 -}
module GMP.Generic where
import List
import Ratio
import Maybe

import Debug.Trace

--------------------------------------------------------------------------------
-- basic data types
--------------------------------------------------------------------------------

-- Formulas
data L a
	=  F | T | Atom Int 
		| Neg (L a) | And (L a) (L a) | Or (L a) (L a)
		| M a [L a]
	deriving (Eq,Show)

-- A sequent is a list of formulas
type Sequent a = [L a]

-- A premise is a list of sequents
type Premise a = [Sequent a] 

-- Logic class: consists of a Modal logic type with a rule for matching clauses
class (Eq a,Show a) => Logic a where 
        -- The matching function for the sequent calculus. Takes the current
        -- sequent returns a list of possible premises (a premise being a list
        -- of sequents)
        match :: Sequent a -> [Premise a]

-- Container class: consists of a container type with rules for accessing it
class (Eq elem,Show elem) => Container cont elem | cont -> elem where 
        -- Is the container empty?
        is_empty :: cont -> Bool
        -- Construct the empty container
        empty_container :: cont
        -- Add an element to the end of a container
        container_add :: cont -> elem -> cont
        -- Add an element to the front of a container
        add_to_container :: elem -> cont -> cont
        -- Merge two containers into one
        container_cons :: cont -> cont -> cont
        -- Get the first element from a container
        get_from_container :: cont -> elem
        -- Remove the first element from a container
        remove_from_container :: cont -> cont

-- Instantiation of container class to lists
instance (Eq a,Show a) => Container [a] a where
	is_empty [] = True
        is_empty (x:xs) = False
	empty_container = []
        container_add cont phi = cont ++ [phi]
        add_to_container phi cont = [phi] ++ cont
        container_cons cont1 cont2 = cont1 ++ cont2
        get_from_container cont = head cont
        remove_from_container cont = tail cont

--------------------------------------------------------------------------------
-- generic functions for containers
--------------------------------------------------------------------------------

-- Remove all elements NOT fulfilling the condition from a container
container_filter :: (Container cont elem) => (elem -> Bool) -> cont -> cont
container_filter cond cont = case is_empty(cont) of 
                 True -> empty_container;
                 False -> case cond (get_from_container cont) of
                    True-> add_to_container (get_from_container cont) (container_filter cond (remove_from_container cont));
                    False-> container_filter cond (remove_from_container cont)

-- Apply function to each element in the container
container_map :: (Container cont1 elem1, Container cont2 elem2) => (elem1 -> elem2) -> cont1 -> cont2
container_map op cont = case is_empty(cont) of
                  True -> empty_container;
                  False -> add_to_container (op (get_from_container cont)) (container_map op (remove_from_container cont));

--------------------------------------------------------------------------------
-- pretty printing functions
--------------------------------------------------------------------------------

-- pretty print formula
pretty :: (Logic a) => L a -> String
pretty F = "F"; pretty T = "T";
pretty (Atom k) = "p" ++ (show k);
pretty (Or (Neg x) y) =  "("++ (pretty x) ++ ") --> (" ++ (pretty y) ++ ")"
pretty (Neg x) = "!" ++  (pretty x)
pretty (Or x y) = "(" ++ (pretty x) ++ ") OR (" ++ (pretty y) ++ ")"
pretty (And x y) = "(" ++ (pretty x) ++ ") AND (" ++ (pretty y) ++ ")"
pretty (M a x) = "[" ++ (show a) ++ "](" ++ (show (map pretty x)) ++ ")"

-- pretty print sequent
pretty_seq :: (Logic a) => Sequent a -> String
pretty_seq [] = "\n\t .. Sequent finished"
pretty_seq (x:xs) = (pretty x) ++ (pretty_seq xs)

