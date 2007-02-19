{-# OPTIONS -fallow-undecidable-instances #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@tzi.de
Stability   :  experimental
Portability :  portable

Definition of signatures for propositional logic

Ref.

Till Mossakowski, Joseph Goguen, Razvan Diaconescu, Andrzej Tarlecki.
What is a Logic?.
In Jean-Yves Beziau (Ed.), Logica Universalis, pp. 113-@133. Birkhäuser.
2005.

-}

module Propositional.Sign where

import qualified Common.Lib.Set as Set
import Common.Id

-- Signatures are just sets
data Sign = Sign {items :: Set.Set Id}
          deriving (Eq, Show)

-- | determines whether a signature is vaild
-- all sets are ok, so glued to true
isLegalSignature :: Sign -> Bool
isLegalSignature _ = True
