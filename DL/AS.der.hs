{- |
Module      :  $Header$
Description :  abstract syntax for DL logic similar to Manchester DL
Copyright   :  Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Abstract syntax for DL logic 
-}

module DL.AS where

-- | CASL-DL Abstract Syntax
-- | based on  the proposition of Manchester OWL Syntax

import Common.Id
import Common.AS_Annotation()
import Common.Doc
import Common.DocUtils

-- DrIFT command
{-! global: UpPos !-}

data DLConcept = DLClassId Id | 
               DLAnd DLConcept DLConcept |
               DLOr DLConcept DLConcept |
               DLNot DLConcept |
               DLOneOf [Id] |
               DLSome DLRel DLConcept | 
               DLHas DLRel DLConcept | 
               DLOnly DLRel DLConcept |
               DLMin DLRel Int |
               DLMax DLRel Int |
               DLExactly DLRel Int |
               DLValue DLRel Id |
               DLThat DLConcept DLConcept |
               DLOnlysome DLRel [DLConcept] |
               DLXor DLConcept DLConcept
               deriving (Show, Ord, Eq)
               
type DLRel = DLConcept

data DLClassProperty = DLSubClassof [DLConcept]
                     | DLEquivalentTo [DLConcept]
                     | DLDisjointWith [DLConcept]
                     deriving (Show, Ord, Eq)

data DLBasicItem = DLClass  Id [DLClassProperty] (Maybe DLPara)|
                   DLValPart Id [Id] (Maybe DLPara)|
                   DLObjectProperty Id (Maybe Id) (Maybe Id)
                                        [DLPropsRel] [DLChars] (Maybe DLPara)|
                   DLDataProperty Id (Maybe Id) (Maybe Id) 
                                      [DLPropsRel] [DLChars] (Maybe DLPara) |                                       
                   DLIndividual Id (Maybe DLType) [DLFacts]
                                    [DLIndRel] (Maybe DLPara)
                   deriving (Show, Ord, Eq)

data DLFacts = DLPosFact (Id,Id) | DLNegFact (Id,Id)
             deriving (Show, Ord, Eq)

data DLType = DLType [Id]
              deriving (Show, Ord, Eq)

data DLChars = DLFunctional | DLInvFuntional | CDSymmetric | DLTransitive
             deriving (Show, Ord, Eq)

data DLIndRel = DLDifferentFrom [Id] |
                DLSameAs [Id]
                deriving (Show, Ord, Eq)

data DLPropsRel = DLSubProperty [Id] |
                  DLInverses [Id]    |
                  DLEquivalent [Id]  |
                  DLDisjoint [Id]
                  deriving (Show, Ord, Eq)

type ISOLangCode = String

data DLPara = DLPara [(ISOLangCode, String)]
					deriving (Show, Ord, Eq)

data DLBasic = DLBasic [DLBasicItem]
             deriving (Show)

instance Pretty DLBasicItem where
    pretty = text . show

instance Pretty DLClassProperty where
    pretty = text . show

instance Pretty DLBasic where
    pretty = text . show

instance Pretty DLConcept where
    pretty = text . show
