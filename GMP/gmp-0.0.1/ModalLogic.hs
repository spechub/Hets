{- | Module     : $Header$
 -  Description : Centralizes the various logics under a default class
 -  Copyright   : (c) Georgel Calin & Lutz Schroeder, DFKI Lab Bremen
 -  License     : Similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
 -  Maintainer  : g.calin@jacobs-university.de
 -  Stability   : provisional
 -  Portability : non-portable (various -fglasgow-exts extensions)
 -
 -  Provides a general modal logic class under which all our logics fall
 -  and its purpose its the centralization of the algorithm apart from the
 -  logic specific parts -}
{-# OPTIONS -fglasgow-exts #-}
module GMP.ModalLogic where

import GMP.GMPAS
import Text.ParserCombinators.Parsec
import qualified Data.Set as Set
import Data.Maybe

-- | Preprocessing flag to set the default modal operator type
data PPflag = Sqr | Ang | None
    deriving Eq

{- | The default modal logic restricted by the functional dependency between
 - the modal application type and the rules of each logic -}
class ModalLogic a b | a -> b, b -> a where
  -- | Preprocess logic specific things (used for Coalition Logic)
  specificPreProcessing :: Formula a -> Maybe (Formula a)
  specificPreProcessing f = Just f
  -- | Primary modal operator flag setting
  flagML :: (Formula a) -> PPflag
  -- | Index parser
  parseIndex :: Parser a
  -- | Rule matching against propositional clause
  matchR :: (ModClause a) -> [b]
  -- | Propositional clause guessing
  guessClause :: b -> [PropClause]
  {- | Default implementation for the (negated) contracted clause generating
   - given a certain pseudovaluation and the set {modal atoms}\{variables} -}
  contrClause :: (Ord a)=>Set.Set(Formula a)->Set.Set(Formula a)->[ModClause a]
  contrClause n ma =
    let p = Set.difference ma n
        pl = perm p
        nl = perm n
    in combineLit pl nl

-- | Return all permutations of a set as a list of lists
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

-- | Combine the positive and negative literals from the possible ones
combineLit :: [[Formula a]] -> [[Formula a]] -> [ModClause a]
combineLit l1 l2 = [Mimplies x y | x <- l1, y <- l2]
