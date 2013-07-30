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
data TypeClass = TypeClass { name :: String, kind :: TypeKind }  deriving (Eq, Ord)

instance Show TypeClass where
	show (TypeClass nam DataTypeKind) = " DataType(" ++ nam ++ ")"
	show (TypeClass nam ClassKind) = " Class(" ++ nam ++ ")"


type Role = String


data PropertyT = PropertyT { sourceRole :: Role
		, sourceType :: TypeClass
		, targetRole :: Role
		, targetType :: TypeClass
		} deriving (Eq, Ord)

instance Show PropertyT where
	show (PropertyT souR souT tarR tarT) = "Property(" ++ souR ++ " :" ++ (show souT) 
					++ "," ++ tarR ++ " :" ++ (show tarT) ++ ") \n"


data LinkT = LinkT { sourceVar :: Role
		, targetVar :: Role
		, property :: PropertyT
		} deriving (Eq, Ord)

instance Show LinkT where
	show (LinkT souV tarV pro) = "Link(" ++ souV ++ " : " ++ (sourceRole pro) ++ " :" ++ (show (sourceType pro)) ++ "," 
				++ tarV ++ " : " ++ (targetRole pro) ++ " :" ++ (show (targetType pro)) ++ ") \n"


data Sign = Sign
    { 	types :: Set.Set TypeClass
	, typeRel :: Rel.Rel TypeClass
	, abstractClasses :: Set.Set TypeClass
	, roles :: Set.Set Role
	, properties :: Set.Set PropertyT
	, instances :: Map.Map String TypeClass
	, links :: Set.Set LinkT
    } deriving (Eq, Ord)

instance Show Sign where
	show (Sign typ tyR abs rol pro ins lin) = 
		"Types = (" ++ (Set.fold ((++) . show) "" typ) ++ ") \n" ++
		"SubRels = (" ++ (foldr ((++) . show) "" (Rel.toList tyR)) ++ ") \n" ++
		"Abs = (" ++ (Set.fold ((++) . show) "" abs) ++ ") \n" ++
		"Roles = (" ++ (Set.fold ((++) . (++ " ")) "" rol) ++ ") \n" ++
		"Properties = (" ++ (Set.fold ((++) . show) "" pro) ++ ") \n" ++
		"Instances = (" ++ (foldr ((++) . show) "" (Map.toList ins)) ++ ") \n" ++
		"Links = (" ++ (Set.fold ((++) . show) "" lin) ++ ") \n"


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
				} deriving (Eq, Ord)

instance Show MultConstr where
	show (MultConstr tc ro) = (show tc) ++ "." ++ ro


data ConstraintType = EQUAL | LEQ | GEQ deriving (Eq, Ord)

instance Show ConstraintType where
	show (EQUAL) = " = "
	show (LEQ) = " <= "
	show (GEQ) = " >= "


data Sen = Sen { constraint :: MultConstr
		, cardinality :: Integer
		, constraintType :: ConstraintType 
		} deriving (Eq, Ord)

instance Show Sen where
	show (Sen con car cty) = (show con) ++ (show cty) ++ (show car) ++ "\n"
