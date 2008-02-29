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

module RelationalScheme.Sign 
        (
            RSIsKey
        ,   RSDatatype(..)
        ,   RSRawSymbol
        ,   RSColumn(..)
        ,   RSTable(..)
        ,   RSTables(..)
        ,   Sign
        ,   RSMorphism(..)
        ,   RSTMap(..)
        ,   emptyRSSign
        ,   isRSSubsig
        ,   concatComma
        ,   idMor
        ,   rsInclusion
        ,   uniteSig
        )
        where

import Common.Id
import Common.AS_Annotation
import Common.Doc
import Common.DocUtils
import RelationalScheme.Keywords
import qualified Data.Set as Set
import qualified Data.Map as Map
import Common.Result

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
                deriving (Eq, Ord)
 
data RSTable = RSTable 
                {
                    t_name  :: Id
                ,   columns :: [RSColumn]
                ,   rsannos :: [Annotation]
                ,   t_keys  :: Set.Set Id
                }
                deriving (Eq, Ord)

data RSTables = RSTables
                    {
                        tables :: Set.Set RSTable
                    }
                deriving (Eq, Ord)

uniteSig :: (Monad m) => RSTables -> RSTables -> m RSTables
uniteSig s1 s2 = return $ RSTables $ (tables s1) `Set.union` (tables s2)
                
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

isRSSubsig  :: RSTables -> RSTables -> Bool
isRSSubsig t1 t2 = t1 <= t2
    
emptyRSSign :: RSTables    
emptyRSSign =  RSTables 
                {
                    tables  = Set.empty
                }

-- ^ id-morphism for RS
idMor :: RSTables -> RSMorphism
idMor t = RSMorphism 
            {
                domain   = t
            ,   codomain = t
            ,   table_map = foldl (\y x -> Map.insert (t_name x) (t_name x) y) Map.empty $ 
                                    Set.toList $ tables t
            ,   column_map = 
                    let 
                        makeRSTMap i =
                           foldl (\y x -> Map.insert (c_name x) (c_name x) y) Map.empty $ 
                                    columns i
                    in
                        foldl (\y x -> Map.insert (t_name x) (RSTMap $ makeRSTMap x) y)
                                Map.empty $ Set.toList $ tables t
            }

rsInclusion :: RSTables -> RSTables -> Result RSMorphism
rsInclusion t1 t2 =
    case t1 `isRSSubsig` t2 of
        False -> fatal_error ((show t1) ++ "\nis not subsignature of\n" ++ (show t2)) nullRange
        True  -> return $ RSMorphism 
            {
                domain   = t1
            ,   codomain = t2
            ,   table_map = foldl (\y x -> Map.insert (t_name x) (t_name x) y) Map.empty $ 
                                    Set.toList $ tables t1
            ,   column_map = 
                    let 
                        makeRSTMap i =
                           foldl (\y x -> Map.insert (c_name x) (c_name x) y) Map.empty $ 
                                    columns i
                    in
                        foldl (\y x -> Map.insert (t_name x) (RSTMap $ makeRSTMap x) y)
                                Map.empty $ Set.toList $ tables t1
            }

-- pretty printing stuff

instance Show RSColumn where
    show c = (if c_key c 
              then rsKey ++ " "
              else "") ++ (show $ c_name c) ++ ":" ++ (show $ c_data c)

instance Show RSTable where
    show t = (show $ t_name t) ++ "(" ++ concatComma (map show $ columns t) ++ ")" 
            
instance Show RSTables where
    show t = rsTables ++ "\n" ++ 
             (unlines $ map show $ Set.toList $ tables t)
                
instance Pretty RSTables where
    pretty = text . show

instance Pretty RSMorphism where
    pretty = text . show
               
concatComma :: [String] -> String
concatComma [] = ""
concatComma (x:[]) = x
concatComma (x:xs) = x ++ ", " ++ concatComma xs


                    