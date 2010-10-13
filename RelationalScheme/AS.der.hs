{- |
Module      :  $Header$
Description :  abstract syntax for Relational Schemes
Copyright   :  Dominik Luecke, Uni Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt or LIZENZ.txt

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
        ,   map_rel
        ,   getRels
        ,   getSignature
        )
        where

import Common.Id
import Common.AS_Annotation
import Common.Doc
import Common.DocUtils
import RelationalScheme.Keywords
import RelationalScheme.Sign
import qualified Data.Map as Map
import Common.Result

-- DrIFT command
{-! global: GetRange !-}

data RSRelType = RSone_to_one | RSone_to_many | RSmany_to_one | RSmany_to_many
                 deriving (Eq, Ord)

-- first Id is TableId, second is columnId
data RSQualId = RSQualId
                {
                  table  :: Id
                , column :: Id
                , q_pos  :: Range
                }
                deriving (Eq, Ord, Show)

data RSRel = RSRel
             {
               r_lhs  :: [RSQualId]
             , r_rhs  :: [RSQualId]
             , r_type :: RSRelType
             , r_pos  :: Range
             }
             deriving (Eq, Ord, Show)

data RSRelationships =  RSRelationships [Annoted RSRel] Range
                        deriving (Eq, Ord, Show)

data RSScheme = RSScheme RSTables RSRelationships Range
                deriving (Eq, Ord, Show)

type Sentence = RSRel

-- Pretty printing stuff

instance Pretty RSScheme where
  pretty (RSScheme t r _) = pretty t $++$ pretty r

instance Pretty RSRelationships where
  pretty (RSRelationships rs _) = if null rs then empty else
    keyword rsRelationships $+$ vcat (map pretty rs)

instance Pretty RSRel where
  pretty (RSRel i1 i2 tp _) =
    let tbl is = case is of
               [] -> empty
               t : _ -> pretty (table t)
             <> brackets (ppWithCommas is)
    in fsep [tbl i1, funArrow, tbl i2, keyword (show tp)]

instance Pretty RSQualId where
  pretty = pretty . column

instance Show RSRelType where
    show r = case r of
        RSone_to_one   -> rs1to1
        RSone_to_many  -> rs1tom
        RSmany_to_one  -> rsmto1
        RSmany_to_many -> rsmtom


map_qualId :: RSMorphism -> RSQualId -> Result RSQualId
map_qualId mor qid =
    let
        (tid, rid, rn) = case qid of
            RSQualId i1 i2 rn1 -> (i1, i2,rn1)
    in maybe (fail "map_qualId") return $ do
            mtid <- Map.lookup tid $ table_map mor
            rmor <- Map.lookup tid $ column_map mor
            mrid <- Map.lookup rid $ col_map rmor
            return $ RSQualId mtid mrid rn


map_rel :: RSMorphism -> RSRel -> Result RSRel
map_rel mor rel =
    let
        (q1, q2, rt, rn) = case rel of
            RSRel qe1 qe2 rte rne -> (qe1, qe2, rte, rne)
    in
      do
        mq1 <- mapM (map_qualId mor) q1
        mq2 <- mapM (map_qualId mor) q2
        return $ RSRel mq1 mq2 rt rn

{-
map_arel :: RSMorphism -> (Annoted RSRel) -> Result (Annoted RSRel)
map_arel mor arel =
    let
        rel = item arel
        (q1, q2, rt, rn) = case rel of
            RSRel qe1 qe2 rte rne -> (qe1, qe2, rte, rne)
    in
      do
        mq1 <- mapM (map_qualId mor) q1
        mq2 <- mapM (map_qualId mor) q2
        return $ arel
                    {
                        item = RSRel mq1 mq2 rt rn
                    }


map_relships :: RSMorphism -> RSRelationships -> Result RSRelationships
map_relships mor rsh =
    let
        (arel, rn) = case rsh of
            RSRelationships arel1 rn1 -> (arel1, rn1)
    in
        do
            orel <- mapM (map_arel mor) arel
            return $ RSRelationships orel rn
-}

-- ^ oo-style getter function for Relations
getRels :: RSScheme -> [Annoted RSRel]
getRels spec = case spec of
            RSScheme _ (RSRelationships rels _) _ -> rels

-- ^ oo-style getter function for signatures
getSignature :: RSScheme -> RSTables
getSignature spec = case spec of
            RSScheme tb _ _ -> tb
