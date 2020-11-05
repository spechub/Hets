{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
{- |
Module      :  ./CSMOF/Sign.hs
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

import Data.Data
import qualified Data.HashMap.Lazy as Map
import qualified Data.Set as Set

import GHC.Generics (Generic)
import Data.Hashable

data TypeKind = DataTypeKind | ClassKind
  deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable TypeKind

instance Pretty TypeKind where
  pretty DataTypeKind = text "datatype"
  pretty ClassKind = text "class"

data TypeClass = TypeClass { name :: String, kind :: TypeKind }
 deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable TypeClass

instance Pretty TypeClass where
  pretty (TypeClass nam _) = text nam


type Role = String


data PropertyT = PropertyT { sourceRole :: Role
                           , sourceType :: TypeClass
                           , targetRole :: Role
                           , targetType :: TypeClass
                           } deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable PropertyT

instance Pretty PropertyT where
  pretty (PropertyT souR souT tarR tarT) = text "property" <> lparen <>
   text souR <+> colon <+> pretty souT <+> comma <+> text tarR <+>
   colon <+> pretty tarT <> rparen

data LinkT = LinkT { sourceVar :: Role
                   , targetVar :: Role
                   , property :: PropertyT
                   } deriving (Show, Eq, Ord, Typeable, Data)

instance Pretty LinkT where
  pretty (LinkT souV tarV pro) = text "link" <> lparen <> text souV <+>
                                 colon <+> text (sourceRole pro) <+> colon <+>
                                 pretty (sourceType pro) <+> comma <+>
                                 text tarV <+> colon <+> text (targetRole pro)
                                 <+> colon <+> pretty (targetType pro) <+>
                                 rparen

data Sign = Sign { types :: Set.Set TypeClass
                 , typeRel :: Rel.Rel TypeClass
                 , abstractClasses :: Set.Set TypeClass
                 , roles :: Set.Set Role
                 , properties :: Set.Set PropertyT
                 , instances :: Map.HashMap String TypeClass
                 , links :: Set.Set LinkT
                 } deriving (Show, Eq, Ord, Typeable, Data)

instance GetRange Sign where
  getRange _ = nullRange
  rangeSpan _ = []

instance Pretty Sign where
  pretty (Sign typ tyR abst rol pro ins lin) =
    Set.fold (($+$) . toType abst) empty typ
    $++$
    foldr (($+$) . toSubRel) empty (Rel.toList tyR)
    $++$
    Set.fold (($+$) . text . ("role " ++)) empty rol
    $++$
    Set.fold (($+$) . pretty) empty pro
    $++$
    foldr (($+$) . toInstance) empty (Map.toList ins)
    $++$
    Set.fold (($+$) . pretty) empty lin

toType :: Set.Set TypeClass -> TypeClass -> Doc
toType setTC (TypeClass nam ki) =
  if Set.member (TypeClass nam ki) setTC then
    text "abstract" <+> pretty ki <+> text nam
  else pretty ki <+> text nam

toSubRel :: (TypeClass, TypeClass) -> Doc
toSubRel (a, b) = pretty a <+> text "<" <+> pretty b

toInstance :: (String, TypeClass) -> Doc
toInstance (a, b) = text "object" <+> text a <+> colon <+> pretty b

emptySign :: Sign
emptySign = Sign { types = Set.empty
                 , typeRel = Rel.empty
                 , abstractClasses = Set.empty
                 , roles = Set.empty
                 , properties = Set.empty
                 , instances = Map.empty
                 , links = Set.empty
                 }


{- signUnion :: Sign -> Sign -> Result Sign
signUnion s1 s2 = return s1
{ rels = Map.unionWith Set.union (rels s1) (rels s2)
, isas = Rel.union (isas s1) (isas s2) } -}

data MultConstr = MultConstr { getType :: TypeClass
                             , getRole :: Role
                             } deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable MultConstr

instance Pretty MultConstr where
  pretty (MultConstr tc ro) = pretty tc <> text "." <> text ro


data ConstraintType = EQUAL | LEQ | GEQ deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable ConstraintType

instance Pretty ConstraintType where
  pretty EQUAL = equals
  pretty LEQ = text "<="
  pretty GEQ = text ">="


data Sen = Sen { constraint :: MultConstr
               , cardinality :: Integer
               , constraintType :: ConstraintType
               } deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable Sen

instance GetRange Sen where
  getRange _ = nullRange
  rangeSpan _ = []

instance Pretty Sen where
  pretty (Sen con car cty) = pretty con <+> pretty cty <+> pretty car
