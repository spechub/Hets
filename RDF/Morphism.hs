{- |
Module      :  $Header$
Description :  RDF Morphism
Copyright   :  (c) Francisc-Nicolae Bungiu, 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.bungiu@jacobs-university.de
Stability   :  provisional
Portability :  portable

Morphisms for RDF
-}

module RDF.Morphism where

import RDF.AS
import RDF.Sign

import Common.DocUtils
import Common.Doc
import Common.Result
import Common.Utils (composeMap)
import Common.Lib.State (execState)
import Common.Lib.MapSet (setToMap)

import Control.Monad
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

data RDFMorphism = RDFMorphism
  { osource :: Sign
  , otarget :: Sign
  , mmaps :: MorphMap
  , pmap :: StringMap
  } deriving (Show, Eq, Ord)

inclRDFMorphism :: Sign -> Sign -> RDFMorphism
inclRDFMorphism s t = RDFMorphism
 { osource = s
 , otarget = t
 , pmap = Map.empty
 , mmaps = Map.empty }

isRDFInclusion :: RDFMorphism -> Bool
isRDFInclusion m = Map.null (pmap m)
  && Map.null (mmaps m) && isSubSign (osource m) (otarget m)
  
legalMor = undefined
composeMor = undefined
  
  
