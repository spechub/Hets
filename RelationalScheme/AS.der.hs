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
import Common.Doc()
import Common.DocUtils()
import RelationalScheme.Keywords

-- DrIFT command
{-! global: UpPos !-}

type RSRelationID = Id
type RSIsKey = Bool

data RSDatatype = RSboolean | RSbinary | RSdate | RSdatetime | RSdecimal | RSfloat |
                  RSinteger | RSstring | RStext | RStime | RStimestamp
                  deriving (Eq, Ord, Show)

data RSRelType = RSone_to_one | RSone_to_many | RSmany_to_one | RSmany_to_many
                 deriving (Eq, Ord, Show)
                  
data RSColumn = RSColumn Id RSDatatype RSIsKey Range
                deriving (Eq, Ord, Show)
 
data RSTable = RSTable Id [RSColumn] Range
                deriving (Eq, Ord, Show)

data RSTables = RSTables [RSTable] Range
                deriving (Eq, Ord, Show)

-- first Id is TableId, second is columnId
data RSQualId = RSQualId Id Id Range
                deriving (Eq, Ord, Show)

data RSRel = RSRel RSQualId RSQualId RSRelType Range
             deriving (Eq, Ord, Show)

data RSRelationships =  RSRelationships [RSRel] Range
                        deriving (Eq, Ord, Show)

data RSScheme = RSScheme (Annoted RSTables) (Annoted RSRelationships) Range
                deriving (Eq, Show)
                