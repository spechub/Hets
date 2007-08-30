{-# OPTIONS -fglasgow-exts #-}
module GMP.ModalLogic where

import GMP.GMPAS
import Text.ParserCombinators.Parsec
import qualified Data.Set as Set

data PPflag = Sqr | Ang | None
    deriving Eq
-------------------------------------------------------------------------------
-- Modal Logic Class
-------------------------------------------------------------------------------
class ModalLogic a b | a -> b, b -> a where
  -- preprocess logic specific things (used for coalition logic)
  processFormula :: Formula a -> Formula a
  processFormula = id
  -- primary modal operator flag
  flagML :: (Formula a) -> PPflag
  -- index parser
  parseIndex :: Parser a
  -- Rho matching
  matchR :: (ModClause a) -> [b]
  -- clause guessing
  guessClause :: b -> [PropClause]
{- default instance for the (negated) contracted clause choosing
 - @ param n : the pseudovaluation
 - @ param ma : the modal atoms (excluding variables)
 - @ return : the list of contracted clauses entailed by h -}
  contrClause :: (Ord a)=>Set.Set(Formula a)->Set.Set(Formula a)->[ModClause a]
  contrClause n ma =
    let p = Set.difference ma n
        pl = perm p
        nl = perm n
    in combineLit pl nl
-------------------------------------------------------------------------------
{- permute the elements of a set
 - @ param s : the set
 - @ return : list of permuted items (stored as list) -}
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
combineLit :: [[Formula a]] -> [[Formula a]] -> [ModClause a]
combineLit l1 l2 = [Mimplies x y | x <- l1, y <- l2]
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
