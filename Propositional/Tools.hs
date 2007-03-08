{-# OPTIONS -fallow-undecidable-instances #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@tzi.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Some helper functions for Propositional Logic
-}

{-
  Ref.

  http://en.wikipedia.org/wiki/Propositional_logic

  Till Mossakowski, Joseph Goguen, Razvan Diaconescu, Andrzej Tarlecki.
  What is a Logic?.
  In Jean-Yves Beziau (Ed.), Logica Universalis, pp. 113-@133. Birkhäuser.
  2005.
-}

module Propositional.Tools 
    (
     flatten                   -- "flattening" of specs
    )
    where
 
import qualified Propositional.AS_BASIC_Propositional as AS_BASIC

-- | flatten \"flattens\" formulae under the assumption of the
-- | semantics of basic specs, this means that we put each
-- | \"clause\" into a single formula for CNF we really will obtain
-- | clauses

flatten :: AS_BASIC.FORMULA -> [AS_BASIC.FORMULA]
flatten f = 
    case f of 
      AS_BASIC.Negation _ _       -> [f]
      AS_BASIC.Disjunction _ _    -> [f]
      AS_BASIC.Implication _ _ _  -> [f]
      AS_BASIC.Equivalence _ _ _  -> [f]
      AS_BASIC.True_atom _        -> [f]
      AS_BASIC.False_atom _       -> [f]
      AS_BASIC.Predication _      -> [f]
      AS_BASIC.Conjunction fs _   -> concat $ map flatten fs
