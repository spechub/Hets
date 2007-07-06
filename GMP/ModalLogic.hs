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
{- default instance for the contracted clause choosing
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
  if (Set.size s <= 1)
  then [Set.toList s]
  else let (x,aux) = Set.deleteFindMin s
           (y,tl) = Set.deleteFindMin aux
       in map (x:) (perm aux) ++ map (y:) (perm (Set.insert x tl))

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
