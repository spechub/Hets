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
        ,   comp_rst_mor
        ,   RSSymbol(..)
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
import Common.Utils
import Control.Monad

type RSIsKey = Bool

data RSDatatype = RSboolean | RSbinary | RSdate | RSdatetime | RSdecimal | RSfloat |
                  RSinteger | RSstring | RStext | RStime | RStimestamp | RSdouble |
                  RSnonPosInteger | RSnonNegInteger | RSlong | RSPointer
                  deriving (Eq, Ord)

type RSRawSymbol = Id

data RSSymbol = STable Id |     -- id of a table
                SColumn
                    Id          -- id of the symbol
                    Id          -- id of the table
                    RSDatatype  -- datatype of the symbol
                    RSIsKey     -- is it a key?
                deriving (Eq,Ord,Show)

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
                ,   t_keys  :: Set.Set (Id, RSDatatype)
                }
                deriving (Eq)

data RSTables = RSTables
                    {
                        tables :: Set.Set RSTable
                    }
                deriving (Eq, Ord)

isRSSubsig  :: RSTables -> RSTables -> Bool
isRSSubsig t1 t2 = t1 <= t2

uniteSig :: (Monad m) => RSTables -> RSTables -> m RSTables
uniteSig s1 s2 =
    if s1 `isRSSubsig` s2
    then
       return $ RSTables $ (tables s1) `Set.union` (tables s2)
    else
        if s2 `isRSSubsig` s1
        then
             return $ RSTables $ (tables s1) `Set.union` (tables s2)
        else
            if s1 `isDisjoint` s2 then
                 return $ RSTables $ (tables s1) `Set.union` (tables s2)
            else
                fail ("Tables " ++ (show s1) ++ " and " ++ (show s2) ++
                    " cannot be united.")

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

-- I hope that this works right, I do not want to debug this
apply_comp_c_map :: Id -> RSMorphism -> RSMorphism -> Result (Id, RSTMap)
apply_comp_c_map i imap imor =
    let
        apply_comp_c_maph :: Id -> RSTMap -> RSMorphism -> Result (Id, RSTMap)
        apply_comp_c_maph ih imaph imorh =
          case Map.lookup ih $ column_map imorh of
            Just iM -> do
                oM <- comp_c_map (col_map imaph) (col_map iM)
                return (ih, RSTMap oM)
            Nothing -> fail "apply_comp_c_map"
    in case Map.lookup i $ column_map imap of
      Just iM -> do
        oM <- apply_comp_c_maph i iM imor
        return $ oM
      Nothing -> fail "apply_comp_c_map,imap"

-- composition of Rel morphisms
comp_rst_mor ::   RSMorphism -> RSMorphism -> Result RSMorphism
comp_rst_mor mor1 mor2 =
    do
        t_map <- composeMap (table_map mor1) (table_map mor2)
        c_map <- mapM (\x -> apply_comp_c_map x mor1 mor2) $ map t_name $
            Set.toList $ tables $ domain $ mor1
        let cm_map = Map.fromList c_map
        return $ RSMorphism
                {
                    domain     = domain mor1
                ,   codomain   = codomain mor2
                ,   table_map  = t_map
                ,   column_map = cm_map
                }

comp_c_map :: (Show b, Ord c, Ord b, Ord a, Monad m) =>
               Map.Map a b -> Map.Map b c -> m (Map.Map a c)
comp_c_map c1 c2 = composeMap c1 c2

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
rsInclusion t1 t2 = return $ RSMorphism
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

instance Pretty RSSymbol where
    pretty = text . show

instance Show RSDatatype where
    show dt = case dt of
        RSboolean       -> rsBool
        RSbinary        -> rsBin
        RSdate          -> rsDate
        RSdatetime      -> rsDatetime
        RSdecimal       -> rsDecimal
        RSfloat         -> rsFloat
        RSinteger       -> rsInteger
        RSstring        -> rsString
        RStext          -> rsText
        RStime          -> rsTime
        RStimestamp     -> rsTimestamp
        RSdouble        -> rsDouble
        RSnonPosInteger -> rsNonPosInteger
        RSnonNegInteger -> rsNonNegInteger
        RSlong          -> rsLong
        RSPointer       -> rsPointer

concatComma :: [String] -> String
concatComma [] = ""
concatComma (x:[]) = x
concatComma (x:xs) = x ++ ", " ++ concatComma xs


-- we need an explicit instance declaration of Ord that
-- correctly deals with tables
isSubtable :: RSTable -> RSTable -> Bool
isSubtable t1 t2 =
    let
        sc1 = Set.fromList $ columns t1
        sc2 = Set.fromList $ columns t2
    in
        t_name t1 == t_name t2 && sc1 `Set.isSubsetOf` sc2

isProperSubtable :: RSTable -> RSTable -> Bool
isProperSubtable t1 t2 =
    let
        sc1 = Set.fromList $ columns t1
        sc2 = Set.fromList $ columns t2
    in
        t_name t1 == t_name t2 && sc1 `Set.isProperSubsetOf` sc2

isDisjoint ::RSTables -> RSTables -> Bool
isDisjoint s1 s2 =
    let
        t1 = Set.map t_name $ (tables) s1
        t2 = Set.map t_name $ (tables) s2
    in
        Set.fold (\x y -> y && (x `Set.notMember` t2)) True t1 &&
        Set.fold (\x y -> y && (x `Set.notMember` t1)) True t2

instance Ord RSTable where
    x <= y = x `isSubtable` y
    x <  y = x `isProperSubtable` y
    x >= y = y `isProperSubtable` x
    x >  y = y `isSubtable` x
