{- |
Module      :  $Header$
Description :  signaturefor Relational Schemes
Copyright   :  Dominik Luecke, Uni Bremen 2008
License     :  similar to LGPL, see Hets/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Signature for Relational Schemes
-}

module RelationalScheme.Sign where

import Common.Id
import Common.AS_Annotation
import Common.Doc
import Common.DocUtils
import RelationalScheme.Keywords
import qualified Data.Set as Set

type RSIsKey = Bool

data RSDatatype = RSboolean | RSbinary | RSdate | RSdatetime | RSdecimal | RSfloat |
                  RSinteger | RSstring | RStext | RStime | RStimestamp
                  deriving (Eq, Ord, Show)
                  
data RSColumn = RSColumn 
                    {
                        c_name :: Id
                    ,   c_data :: RSDatatype
                    ,   c_key  :: RSIsKey
                    ,   c_pos  :: Range    
                    }
                deriving (Eq, Ord, Show)
 
data RSTable = RSTable 
                {
                    t_name  :: Id
                ,   columns :: [RSColumn]
                ,   t_pos   :: Range
                ,   rsannos :: [Annotation]
                ,   t_keys  :: Set.Set Id
                }
                deriving (Eq, Ord, Show)

data RSTables = RSTables
                    {
                        tables :: Set.Set RSTable
                    ,   rst_pos :: Range
                    }
                deriving (Eq, Ord, Show)

instance Pretty RSTables where
    pretty = text . show
                
type Sign = RSTables
                