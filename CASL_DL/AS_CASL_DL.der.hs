{- |
Module      :  $Header$
Description :  abstract syntax for CASL_DL logic extension of CASL
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2004, Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Abstract syntax for CASL_DL logic extension of CASL
  Only the added syntax is specified
-}

module CASL_DL.AS_CASL_DL where

import Common.Id
import Common.AS_Annotation
import CASL.AS_Basic_CASL
import Common.Doc
import Common.DocUtils

-- DrIFT command
{-! global: UpPos !-}

type DL_BASIC_SPEC = BASIC_SPEC () () DL_FORMULA

type AnDLFORM = Annoted (FORMULA DL_FORMULA)

data CardType = CMin | CMax | CExact deriving (Eq, Ord)

minCardinalityS, maxCardinalityS, cardinalityS :: String
cardinalityS = "cardinality"
minCardinalityS = "minC" ++ tail cardinalityS
maxCardinalityS = "maxC" ++ tail cardinalityS

instance Show CardType where
    show ct = case ct of
        CMin -> minCardinalityS
        CMax -> maxCardinalityS
        CExact -> cardinalityS

-- | for a detailed specification of all the components look into the sources
data DL_FORMULA =
    Cardinality CardType
                PRED_SYMB -- refers to a declared (binary) predicate
                (TERM DL_FORMULA)
                -- this term is restricted to constructors
                -- denoting a (typed) variable
                (TERM DL_FORMULA)
               -- the second term is restricted to an Application denoting
               -- a literal of type nonNegativeInteger (Nat)
                Range
               -- position of keyword, brackets, parens and comma
             deriving (Eq, Ord, Show)

caslDLCardTypes :: [CardType]
caslDLCardTypes = [CExact, CMin, CMax]

casl_DL_reserved_words :: [String]
casl_DL_reserved_words = map show caslDLCardTypes


-- | CASL-DL Abstract Syntax
-- | based on  the proposition of Manchester OWL Syntax

data CSConcept = CSClassId Id | 
               CSAnd CSConcept CSConcept |
               CSOr CSConcept CSConcept |
               CSNot CSConcept |
               CSOneOf [Id] |
               CSSome CSRel CSConcept | 
               CSOnly CSRel CSConcept |
               CSMin CSRel Int |
               CSMax CSRel Int |
               CSExactly CSRel Int |
               CSValue CSRel Id |
               CSThat CSConcept CSConcept |
               CSOnlysome CSRel [CSConcept] |
               CSXor CSConcept CSConcept
               deriving (Show)
               
type CSRel = CSConcept

data CSClassProperty = CSSubClassof CSConcept 
                     | CSEquivalentTo CSConcept 
                     | CSDisjointWith CSConcept
                     deriving (Show)

data CSBasicItem = CSClass  Id [CSClassProperty] |
                   CSValPart Id [Id] |
                   CSObjectProperty Id (Maybe Id) (Maybe Id)
                                        [CSPropsRel] |
                   CSIndividual Id (Maybe CSType) [(Id,Id)]
                                    [CSIndRel]
                   deriving (Show)

data CSType = CSType [Id]
              deriving (Show)

data CSIndRel = CSDifferentFrom [Id]
                deriving (Show)

data CSPropsRel = CSSubProperty [Id] |
                  CSInverses [Id]
                  deriving (Show)

data CSBasic = CSBasic [CSBasicItem]
             deriving (Show)

instance Pretty CSBasicItem where
    pretty = text . show

instance Pretty CSClassProperty where
    pretty = text . show

instance Pretty CSBasic where
    pretty = text . show

instance Pretty CSConcept where
    pretty = text . show

-- parser will need 7 functions: concept1, concept2, concept3, concept4, classProperty, basicItem, basicSpec
