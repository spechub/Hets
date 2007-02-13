{-# OPTIONS -fallow-undecidable-instances #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@tzi.de
Stability   :  experimental
Portability :  portable

Definition of morphisms for propositional logic
-}

module Propositional.Morphism where 

import qualified Common.InjMap as InjMap
import qualified Common.Lib.Set as Set
import Propositional.Sign as Sign
import Common.Id

type PropMap = InjMap.InjMap Id Id

data Morphism = Morphism
    {
       source :: Sign
     , target :: Sign
     , propMap :: PropMap
    } deriving (Eq, Show)

idMor :: Sign -> Morphism
idMor a = Morphism 
          { source = a
          , target = a
          , propMap = makeIdMor $ items a
          }

makeIdMor :: (Ord a) => Set.Set a -> InjMap.InjMap a a
makeIdMor a = Set.fold (\x -> InjMap.insert x x) InjMap.empty a
