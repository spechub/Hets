{-# OPTIONS -fglasgow-exts #-}
module ModalLogic where

import GMPAS
import Text.ParserCombinators.Parsec
import qualified Data.Set as Set

data PPflag = Sqr | Ang | None
    deriving Eq
-------------------------------------------------------------------------------
-- Modal Logic Class
-------------------------------------------------------------------------------
class ModalLogic a b | a -> b, b -> a where
  contrClause :: Set.Set (Formula a) -> Set.Set (Formula a) -> [RoClause a]
--    OrderIns :: (Formula a) -> Bool                 -- order insensitivity flag
  flagML :: (Formula a) -> PPflag              -- primary modal operator flag
  parseIndex :: Parser a                                      -- index parser
--    matchRO :: [MATV a] -> [b]                                 -- RO matching
  matchRO :: (RoClause a) -> [b]
  guessClause :: b -> [Clause]                             -- clause guessing
-------------------------------------------------------------------------------
{- default instance for the contracted clause (negated) choosing
 - @ param n : the pseudovaluation
 - @ param ma : the modal atoms (excluding variables)
 - @ return : the list of contracted clauses entailed by h -}
contrClause n ma =
  let p = Set.difference ma n
      pl = perm p
      nl = perm n
  in combineLit pl nl
{- permute the elements of a set
 - @ param s : the set
 - @ return : list of permuted items stored as list -}
perm :: (Ord t) => Set.Set t -> [[t]]
perm s =
  let perms l =
        case l of
          [] -> [[]]
          xs -> [x : ps | (x,ys) <- selections xs, ps <- perms ys]
      selections l =
        case l of 
          []     -> []
          x : xs -> (x,xs) : [(y,x:ys) | (y,ys) <- selections xs]
  in perms (Set.toList s)
{- combine the positive and negative literals from the possible ones
 - @ param l1 : list of modal atoms
 - @ param l2 : list of modal atoms
 - @ return : combined lists -}
combineLit :: [[Formula a]] -> [[Formula a]] -> [RoClause a]
combineLit l1 l2 =
  let assoc e l =
    case l of
      []  -> []
      h:t -> Implies (e,h) : (assoc e t)
  in case l1 of
    []   -> []
    x:xs -> (assoc x l2) ++ (combineLit xs l2)
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
