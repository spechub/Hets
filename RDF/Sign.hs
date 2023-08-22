{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./RDF/Sign.hs
Copyright   :  Francisc-Nicolae Bungiu, Jacobs University Bremen
License     :  GPLv2 or higher, see LICENSE.txt

RDF signature and sentences
-}

module RDF.Sign where

import RDF.AS
import Common.Result
import Data.Data
import qualified Data.Set as Set

data Sign = Sign
    { subjects :: Set.Set Term
    , predicates :: Set.Set Term
    , objects :: Set.Set Term
    } deriving (Show, Eq, Ord, Typeable, Data)

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

uniteSign :: Sign -> Sign -> Result Sign
uniteSign s1 s2 = return $ addSign s1 s2

symOf :: Sign -> Set.Set RDFEntity
symOf s = Set.unions
  [ Set.map (RDFEntity SubjectEntity) $ subjects s
  , Set.map (RDFEntity PredicateEntity) $ predicates s
  , Set.map (RDFEntity ObjectEntity) $ objects s ]
