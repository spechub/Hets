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

module RelationalScheme.AS 
        (
            RSRelType(..)
        ,   RSQualId(..)
        ,   RSRel(..)
        ,   RSRelationships(..)
        ,   RSScheme(..)
        ,   Sentence
        )
        where

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
                deriving (Eq, Ord)

data RSRel = RSRel [RSQualId] [RSQualId] RSRelType Range
             deriving (Eq, Ord)

data RSRelationships =  RSRelationships [Annoted RSRel] Range
                        deriving (Eq, Ord)

data RSScheme = RSScheme RSTables RSRelationships Range
                deriving (Eq, Ord)

type Sentence = RSRel

-- Pretty printing stuff

instance Show RSScheme where
    show s = case s of
                RSScheme t r _ -> (show t) ++ "\n" ++ (show r)

instance Show RSRelationships where
    show r = case r of
                RSRelationships r1 _ -> 
                    case r1 of 
                        [] -> ""
                        _  -> rsRelationships ++ "\n" ++
                                        (unlines $ map (show . item) r1)

instance Show RSRel where
    show r = case r of
        RSRel i1 i2 tp _ -> (concatComma $ map show i1) ++ " " ++ rsArrow ++ " "++
                            (concatComma $ map show i2) ++ " " ++ show tp

instance Show RSQualId where
    show q = case q of
        RSQualId i1 i2 _ -> (show i1) ++ "." ++ (show i2)

instance Pretty RSScheme where
    pretty = text . show

instance Pretty RSRel where
    pretty = text . show  
                  