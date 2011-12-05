{- |
Module      :  $Header$
Copyright   :  Francisc-Nicolae Bungiu, Jacobs University Bremen
License     :  GPLv2 or higher, see LICENSE.txt

RDF signature and sentences
-}

module RDF.Sign where

import OWL2.AS
import RDF.AS
import qualified Data.Set as Set
import qualified Data.Map as Map
import Common.Id
import Common.Result
import Common.Doc
import Common.DocUtils

data Sign = Sign
    { subjects :: Set.Set IRI
    , predicates :: Set.Set IRI
    , objects :: Set.Set IRI
    } deriving (Show, Eq, Ord)


emptySign :: Sign
emptySign = Sign
  { subjects = Set.empty
  , predicates = Set.empty
  , objects = Set.empty
  }


diffSig :: Sign -> Sign -> Sign
diffSig a b =
    a { subjects = subjects a `Set.difference` subjects b
      , predicates = predicates a `Set.difference` predicates b
      , objects = objects a `Set.difference` objects b
      }

addSign :: Sign -> Sign -> Sign
addSign toIns totalSign = totalSign
    { subjects = Set.union (subjects totalSign) (subjects toIns)
    , predicates = Set.union (predicates totalSign) (predicates toIns)
    , objects = Set.union (objects totalSign) (objects toIns)
    }

isSubSign :: Sign -> Sign -> Bool
isSubSign a b =
    Set.isSubsetOf (subjects a) (subjects b)
       && Set.isSubsetOf (predicates a) (predicates b)
       && Set.isSubsetOf (objects a) (objects b)
