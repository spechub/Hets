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
import Data.Map as Map

type RSIsKey = Bool

data RSDatatype = RSboolean | RSbinary | RSdate | RSdatetime | RSdecimal | RSfloat |
                  RSinteger | RSstring | RStext | RStime | RStimestamp | RSdouble |
                  RSnonPosInteger | RSnonNegInteger | RSlong
                  deriving (Eq, Ord, Show)
                  
type RSRawSymbol = Id                  
                  
data RSColumn = RSColumn 
                    {
                        c_name :: Id
                    ,   c_data :: RSDatatype
                    ,   c_key  :: RSIsKey
                    }
                deriving (Eq, Ord, Show)
 
data RSTable = RSTable 
                {
                    t_name  :: Id
                ,   columns :: [RSColumn]
                ,   rsannos :: [Annotation]
                ,   t_keys  :: Set.Set Id
                }
                deriving (Eq, Ord, Show)

data RSTables = RSTables
                    {
                        tables :: Set.Set RSTable
                    }
                deriving (Eq, Ord, Show)

instance Pretty RSTables where
    pretty = text . show
                
type Sign = RSTables
                
data RSTMap = RSTMap 
                {
                   col_map  :: Map.Map Id Id
                }      
                deriving (Eq, Ord, Show)      
                
data RSMorphism = RSMorphism
                    {
                        domain     :: RSTables
                    ,   codomain   :: RSTables
                    ,   table_map  :: Map.Map Id Id
                    ,   column_map :: Map.Map Id RSTMap    
                    }       
                    deriving (Eq, Ord, Show)

instance Pretty RSMorphism where
    pretty = text . show
    
emptyRSSign :: RSTables    
emptyRSSign =  RSTables 
                {
                    tables  = Set.empty
                }
                
isRSSubsig  :: RSTables -> RSTables -> Bool
isRSSubsig t1 t2 = t1 <= t2

                    