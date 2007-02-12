{-# OPTIONS -fallow-undecidable-instances #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

Definition of morphisms for propositional logic
-}

module Propositional.Morphism where 

import qualified Common.Lib.Set as Set
import qualified Common.Lib.Map as Map
import Propositional.Sign as Sign
import Common.Id

type PropMap = Map.Map Sign Sign

data Morphism = Morphism
    {
       source :: Sign
     , target :: Sign
     , propMap :: PropMap
    } deriving (Eq, Show)
