{-# LINE 1 "Reduce/Morhpism.hs" #-}
{- |
Module      :  $Header$
Description :  Abstract syntax for reduce
Copyright   :  (c) Dominik Dietrich, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  dominik.dietrich@dfki.de
Stability   :  experimental
Portability :  portable

this file defines morhpisms for the reduce logic. A morphism is a mapping of operator symbols
-}


module Reduce.Morphism
  ( Morphism (..)               -- datatype for Morphisms
  , pretty                      -- pretty printing
  , idMor                       -- identity morphism
  , isLegalMorphism             -- check if morhpism is ok
  , composeMor                  -- composition
  , inclusionMap                -- inclusion map
  , mapSentence                 -- map of sentences
  , mapSentenceH                -- map of sentences, without Result type
  , applyMap                    -- application function for maps
  , applyMorphism               -- application function for morphism
  , morphismUnion
  ) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Reduce.Sign as Sign
import qualified Common.Result as Result
import Propositional.AS_BASIC_Reduce 
import Common.Id as Id
import Common.Result
import Common.Doc
import Common.DocUtils

-- | The datatype for morphisms in reduce logic as maps of sets
data Morphism = Morphism
  { source :: Sign
  , target :: Sign
  , operatorMap :: Map.Map Id Id
  } deriving (Eq, Ord, Show)

instance Pretty Morphism where
    pretty = printMorphism

-- | Constructs an id-morphism
idMor :: Sign -> Morphism
idMor a = inclusionMap a a

-- | checks whether a given morphism is legal
isLegalMorhpism Morphism -> Bool
isLegalMorphism _ = true

-- | calculates the composition of two morhpisms f:X->Y, g:Y->Z
composeMor :: Morphism -> Morphism -> Result Morphism
composeMor f g =
  let fSource = source f
      gTarget = target g
      fMap    = operatorMap f
      gMap    = operatorMap g
  in return Morphism
  { source = fSource
  , target = gTarget
  , operatorMap = if Map.null gMap then fMap else
      Set.fold ( \ i -> let j = applyMap gMap (applyMap fMap i) in
                        if i == j then id else Map.insert i j)
                                  Map.empty $ items fSource }


-- inclusionMap                -- inclusion map
-- mapSentence                 -- map of sentences
-- mapSentenceH                -- map of sentences, without Result type
-- applyMap                    -- application function for maps
-- applyMorphism               -- application function for morphism
-- morphismUnion

