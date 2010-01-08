{- |
Module      :  $Header$
Description :  Some additional helper functions
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Some helper functions for Propositional Logic
-}

{-
  Ref.

  http://en.wikipedia.org/wiki/Propositional_logic

  Till Mossakowski, Joseph Goguen, Razvan Diaconescu, Andrzej Tarlecki.
  What is a Logic?.
  In Jean-Yves Beziau (Ed.), Logica Universalis, pp. 113-@133. Birkhaeuser.
  2005.
-}

module Propositional.Tools
    ( flatten                   -- "flattening" of specs
    , flattenDis                -- "flattening" of disjunctions
    , negateFormula
    ) where

import Common.Id
import Propositional.AS_BASIC_Propositional

-- | the flatten functions use associtivity to "flatten" the syntax
-- | tree of the formulae

-- | flatten \"flattens\" formulae under the assumption of the
-- | semantics of basic specs, this means that we put each
-- | \"clause\" into a single formula for CNF we really will obtain
-- | clauses

flatten :: FORMULA -> [FORMULA]
flatten f = case f of
      Conjunction fs _ -> concatMap flatten fs
      _ -> [f]

-- | "flattening" for disjunctions
flattenDis :: FORMULA -> [FORMULA]
flattenDis f = case f of
      Disjunction fs _ -> concatMap flattenDis fs
      _ -> [f]

-- | negate a formula
negateFormula :: FORMULA -> FORMULA
negateFormula f = case f of
  False_atom ps -> True_atom ps
  True_atom ps -> False_atom ps
  Negation nf _ -> nf
  _ -> Negation f nullRange
