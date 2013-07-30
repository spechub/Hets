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

import CSMOF.As ()

import qualified Common.Lib.Rel as Rel

import Common.Doc
import Common.DocUtils
import Common.Id

import qualified Data.Map as Map
import qualified Data.Set as Set

data TypeKind = DataTypeKind | ClassKind  deriving (Show, Eq, Ord)

instance Pretty TypeKind where
  pretty DataTypeKind = text "DataType"
  pretty ClassKind = text "Class"

data TypeClass = TypeClass { name :: String, kind :: TypeKind }  deriving (Show, Eq, Ord)

instance Pretty TypeClass where
  pretty (TypeClass nam DataTypeKind) = space <> text "DataType" <> lparen <> text nam <> rparen
  pretty (TypeClass nam ClassKind) = space <> text "Class" <> lparen <> text nam <> rparen


type Role = String


data PropertyT = PropertyT { sourceRole :: Role
                           , sourceType :: TypeClass
                           , targetRole :: Role
                           , targetType :: TypeClass
                           } deriving (Show, Eq, Ord)

instance Pretty PropertyT where
  pretty (PropertyT souR souT tarR tarT) = text "Property" <> lparen <> text souR <+> colon <> (pretty souT) 
                                           <> comma <> text tarR <+> colon <> (pretty tarT) <> rparen


data LinkT = LinkT { sourceVar :: Role
                   , targetVar :: Role
                   , property :: PropertyT
                   } deriving (Show, Eq, Ord)

instance Pretty LinkT where
  pretty (LinkT souV tarV pro) = text "Link" <> lparen <> text souV <+> colon <+> 
                                 text (sourceRole pro) <+> colon <> pretty (sourceType pro) <> comma 
                                 <> text tarV <+> colon <> text (targetRole pro) <+> colon <> (pretty (targetType pro)) <> rparen


data Sign = Sign { types :: Set.Set TypeClass
                 , typeRel :: Rel.Rel TypeClass
                 , abstractClasses :: Set.Set TypeClass
                 , roles :: Set.Set Role
                 , properties :: Set.Set PropertyT
                 , instances :: Map.Map String TypeClass
                 , links :: Set.Set LinkT
                 } deriving (Show, Eq, Ord)

instance GetRange Sign where
  getRange _ = nullRange
  rangeSpan _ = []      

instance Pretty Sign where
  pretty (Sign typ tyR abst rol pro ins lin) = 
    text "Types" <+> equals <+> lparen <> (Set.fold ((<>) . pretty) empty typ) <> rparen $++$
    text "SubRels" <+> equals <+> lparen <> (foldr ((<>) . pretty) empty (Rel.toList tyR)) <> rparen $++$
    text "Abs" <+> equals <+> lparen <> (Set.fold ((<>) . pretty) empty abst) <> rparen $++$
    text "Roles" <+> equals <+> lparen <> (Set.fold ((<+>) . text) empty rol) <> rparen $++$
    text "Properties" <+> equals <+> lparen <> (Set.fold ((<>) . pretty) empty pro) <> rparen $++$
    text "Instances" <+> equals <+> lparen <> (foldr ((<>) . pretty) empty (Map.toList ins)) <> rparen $++$
    text "Links" <+> equals <+> lparen <> (Set.fold ((<>) . pretty) empty lin) <> rparen


emptySign :: Sign
emptySign = Sign { types = Set.empty
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
                             } deriving (Show, Eq, Ord)

instance Pretty MultConstr where
  pretty (MultConstr tc ro) = pretty tc <> text "." <> text ro


data ConstraintType = EQUAL | LEQ | GEQ deriving (Show, Eq, Ord)

instance Pretty ConstraintType where
  pretty EQUAL = equals
  pretty LEQ = text "<="
  pretty GEQ = text ">="


data Sen = Sen { constraint :: MultConstr
               , cardinality :: Integer
               , constraintType :: ConstraintType 
               } deriving (Show, Eq, Ord)

instance GetRange Sen where
  getRange _ = nullRange
  rangeSpan _ = []      

instance Pretty Sen where
  pretty (Sen con car cty) = pretty con <+> pretty cty <+> pretty car
