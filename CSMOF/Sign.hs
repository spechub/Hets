{- |
Module      :  $Header$
Description :  CSMOF signature and sentences
Copyright   :  (c) Daniel Calegari Universidad de la Republica, Uruguay 2013
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  dcalegar@fing.edu.uy
Stability   :  provisional
Portability :  portable
-}

module CSMOF.Sign where

import CSMOF.As

import qualified Common.Lib.Rel as Rel

import qualified Data.Map as Map
import qualified Data.Set as Set

data TypeKind = DataTypeKind | ClassKind  deriving (Show, Eq, Ord)
data TypeClass = TypeClass { name :: String, kind :: TypeKind }  deriving (Show, Eq, Ord)
type Role = String

data PropertyT = PropertyT { sourceRole :: Role
		, sourceType :: TypeClass
		, targetRole :: Role
		, targetType :: TypeClass
		} deriving (Show, Eq, Ord)

data LinkT = LinkT { sourceVar :: Role
		, targetVar :: Role
		, property :: PropertyT
		} deriving (Show, Eq, Ord)



data Sign = Sign
    { 	types :: Set.Set TypeClass
	, typeRel :: Rel.Rel TypeClass
	, abstractClasses :: Set.Set TypeClass
	, roles :: Set.Set Role
	, properties :: Set.Set PropertyT
	, instances :: Map.Map String TypeClass
	, links :: Set.Set LinkT
    } deriving (Eq, Ord, Show)


emptySign :: Sign
emptySign = Sign
    { types = Set.empty
	, typeRel = Rel.empty
	, abstractClasses = Set.empty
	, roles = Set.empty
	, properties = Set.empty
	, instances = Map.empty
	, links = Set.empty
    }


-- signUnion :: Sign -> Sign -> Result Sign
-- signUnion s1 s2 = return s1
--   { rels = Map.unionWith Set.union (rels s1) (rels s2)
--  , isas = Rel.union (isas s1) (isas s2) }

data MultConstr = MultConstr { getType :: TypeClass
				, getRole :: Role
				} deriving (Eq, Ord, Show)

data ConstraintType = EQUAL | LEQ | GEQ deriving (Eq, Ord, Show)

data Sen = Sen { constraint :: MultConstr
		, cardinality :: Integer
		, constraintType :: ConstraintType 
		} deriving (Eq, Ord, Show)

