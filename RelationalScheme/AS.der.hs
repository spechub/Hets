{- |
Module      :  $Header$
Description :  abstract syntax for Relational Schemes
Copyright   :  Dominik Luecke, Uni Bremen 2008
License     :  similar to LGPL, see Hets/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Abstract syntax for Relational Schemes
-}

module RelationalScheme.AS where

import Common.Id
import Common.AS_Annotation
import Common.Doc
import Common.DocUtils
import RelationalScheme.Keywords
import RelationalScheme.Sign

-- DrIFT command
{-! global: UpPos !-}

data RSRelType = RSone_to_one | RSone_to_many | RSmany_to_one | RSmany_to_many
                 deriving (Eq, Ord, Show)

-- first Id is TableId, second is columnId
data RSQualId = RSQualId Id Id Range
                deriving (Eq, Ord, Show)

data RSRel = RSRel [RSQualId] [RSQualId] RSRelType Range
             deriving (Eq, Ord, Show)

data RSRelationships =  RSRelationships [Annoted RSRel] Range
                        deriving (Eq, Show)

data RSScheme = RSScheme RSTables RSRelationships Range
                deriving (Eq, Show)

type Sentence = RSRel

instance Pretty RSScheme where
    pretty = text . show

instance Pretty RSRel where
    pretty = text . show  
                  