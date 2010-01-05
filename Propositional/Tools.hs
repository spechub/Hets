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
    ) where

import qualified Propositional.AS_BASIC_Propositional as AS_BASIC

-- | the flatten functions use associtivity to "flatten" the syntax
-- | tree of the formulae

-- | flatten \"flattens\" formulae under the assumption of the
-- | semantics of basic specs, this means that we put each
-- | \"clause\" into a single formula for CNF we really will obtain
-- | clauses

flatten :: AS_BASIC.FORMULA -> [AS_BASIC.FORMULA]
flatten f = case f of
      AS_BASIC.Conjunction fs _ -> concatMap flatten fs
      _ -> [f]

-- | "flattening" for disjunctions
flattenDis :: AS_BASIC.FORMULA -> [AS_BASIC.FORMULA]
flattenDis f = case f of
      AS_BASIC.Disjunction fs _ -> concatMap flattenDis fs
      _ -> [f]
