{- |
Module      :  $Header$
Description :  signaturefor Relational Schemes
Copyright   :  Dominik Luecke, Uni Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Signature for Relational Schemes
-}

module RelationalScheme.Sign
        ( RSIsKey
        , RSDatatype (..)
        , RSRawSymbol
        , RSColumn (..)
        , RSTable (..)
        , RSTables (..)
        , Sign
        , RSMorphism (..)
        , RSTMap (..)
        , emptyRSSign
        , isRSSubsig
        , idMor
        , rsInclusion
        , uniteSig
        , comp_rst_mor
        , RSSymbol (..)
        )
        where

import RelationalScheme.Keywords

import Common.AS_Annotation
import Common.Doc
import Common.DocUtils
import Common.Id
import Common.Result
import Common.Utils

import qualified Data.Map as Map
import qualified Data.Set as Set

type RSIsKey = Bool

data RSDatatype
  = RSboolean | RSbinary | RSdate | RSdatetime | RSdecimal | RSfloat
  | RSinteger | RSstring | RStext | RStime | RStimestamp | RSdouble
  | RSnonPosInteger | RSnonNegInteger | RSlong | RSPointer
    deriving (Eq, Ord)

type RSRawSymbol = Id

data RSSymbol = STable Id |     -- id of a table
                SColumn
                    Id          -- id of the symbol
                    Id          -- id of the table
                    RSDatatype  -- datatype of the symbol
                    RSIsKey     -- is it a key?
                deriving (Eq, Ord, Show)

instance GetRange RSSymbol

data RSColumn = RSColumn
                    { c_name :: Id
                    , c_data :: RSDatatype
                    , c_key :: RSIsKey
                    }
                deriving (Eq, Ord, Show)

data RSTable = RSTable
                { t_name :: Id
                , columns :: [RSColumn]
                , rsannos :: [Annotation]
                , t_keys :: Set.Set (Id, RSDatatype)
                }
                deriving Show

data RSTables = RSTables
                    {
                        tables :: Set.Set RSTable
                    }
                deriving (Eq, Ord, Show)

instance GetRange RSTables

isRSSubsig :: RSTables -> RSTables -> Bool
isRSSubsig t1 t2 = t1 <= t2

uniteSig :: (Monad m) => RSTables -> RSTables -> m RSTables
uniteSig s1 s2 =
    if s1 `isRSSubsig` s2 || s2 `isRSSubsig` s1 || s1 `isDisjoint` s2
    then return $ RSTables $ tables s1 `Set.union` tables s2
    else fail $ "Tables " ++ showDoc s1 "\nand "
             ++ showDoc s2 "\ncannot be united."

type Sign = RSTables

data RSTMap = RSTMap
                {
                   col_map :: Map.Map Id Id
                }
                deriving (Eq, Ord, Show)

data RSMorphism = RSMorphism
                    { domain :: RSTables
                    , codomain :: RSTables
                    , table_map :: Map.Map Id Id
                    , column_map :: Map.Map Id RSTMap
                    }
                    deriving (Eq, Ord, Show)

-- I hope that this works right, I do not want to debug this
apply_comp_c_map :: RSTable -> Map.Map Id Id -> RSMorphism -> RSMorphism
                 -> (Id, RSTMap)
apply_comp_c_map rst t_map imap imor =
    let i = t_name rst
        c2 = column_map imor
    in case Map.lookup i $ column_map imap of
      Just iM -> case Map.lookup (Map.findWithDefault i i t_map) c2 of
        Just iM2 ->
          let c_set = Map.fromList . map (\ c -> (c_name c, ())) $ columns rst
              oM = composeMap c_set (col_map iM) (col_map iM2)
          in (i, RSTMap oM)
        Nothing -> (i, iM)
      Nothing -> (i, Map.findWithDefault (RSTMap Map.empty)
                       (Map.findWithDefault i i t_map) c2)

-- composition of Rel morphisms
comp_rst_mor :: RSMorphism -> RSMorphism -> Result RSMorphism
comp_rst_mor mor1 mor2 =
        let d1 = domain mor1
            t1 = Set.toList $ tables d1
            t_set = Map.fromList $ map (\ t -> (t_name t, ())) t1
            t_map = composeMap t_set (table_map mor1) (table_map mor2)
            cm_map = Map.fromList
              $ map (\ x -> apply_comp_c_map x t_map mor1 mor2) t1
        in return RSMorphism
                { domain = d1
                , codomain = codomain mor2
                , table_map = t_map
                , column_map = cm_map
                }

emptyRSSign :: RSTables
emptyRSSign = RSTables
                {
                    tables = Set.empty
                }

-- ^ id-morphism for RS
idMor :: RSTables -> RSMorphism
idMor t = RSMorphism
            { domain = t
            , codomain = t
            , table_map = foldl (\ y x -> Map.insert (t_name x) (t_name x) y)
                          Map.empty $ Set.toList $ tables t
            , column_map =
                    let
                        makeRSTMap i =
                           foldl (\ y x -> Map.insert (c_name x) (c_name x) y)
                                 Map.empty $ columns i
                    in
                        foldl (\ y x -> Map.insert (t_name x)
                                        (RSTMap $ makeRSTMap x) y)
                                Map.empty $ Set.toList $ tables t
            }

rsInclusion :: RSTables -> RSTables -> Result RSMorphism
rsInclusion t1 t2 = return RSMorphism
            { domain = t1
            , codomain = t2
            , table_map = foldl (\ y x -> Map.insert (t_name x) (t_name x) y)
                          Map.empty $ Set.toList $ tables t1
            , column_map =
                    let
                        makeRSTMap i =
                           foldl (\ y x -> Map.insert (c_name x) (c_name x) y)
                                 Map.empty $ columns i
                    in
                        foldl (\ y x -> Map.insert (t_name x)
                                        (RSTMap $ makeRSTMap x) y)
                                Map.empty $ Set.toList $ tables t1
            }

-- pretty printing stuff

instance Pretty RSColumn where
    pretty c = (if c_key c then keyword rsKey else empty) <+>
       pretty (c_name c) <+> colon <+> pretty (c_data c)

instance Pretty RSTable where
    pretty t = pretty (t_name t) <> parens (ppWithCommas $ columns t)
               $+$ printAnnotationList (rsannos t)

instance Pretty RSTables where
    pretty t = keyword rsTables $+$ vcat (map pretty $ Set.toList $ tables t)

instance Pretty RSTMap where
    pretty = pretty . col_map

instance Pretty RSMorphism where
    pretty m = pretty (domain m) $+$ mapsto <+> pretty (codomain m)
                $+$ pretty (table_map m) $+$ pretty (column_map m)

instance Pretty RSSymbol where
    pretty s = case s of
      STable i -> pretty i
      SColumn i _ t k -> pretty $ RSColumn i t k

instance Show RSDatatype where
    show dt = case dt of
        RSboolean -> rsBool
        RSbinary -> rsBin
        RSdate -> rsDate
        RSdatetime -> rsDatetime
        RSdecimal -> rsDecimal
        RSfloat -> rsFloat
        RSinteger -> rsInteger
        RSstring -> rsString
        RStext -> rsText
        RStime -> rsTime
        RStimestamp -> rsTimestamp
        RSdouble -> rsDouble
        RSnonPosInteger -> rsNonPosInteger
        RSnonNegInteger -> rsNonNegInteger
        RSlong -> rsLong
        RSPointer -> rsPointer

instance Pretty RSDatatype where
  pretty = keyword . show

{- we need an explicit instance declaration of Eq and Ord that
correctly deals with tables -}
instance Ord RSTable where
  compare t1 t2 =
    compare (t_name t1, Set.fromList $ columns t1)
            (t_name t2, Set.fromList $ columns t2)

instance Eq RSTable where
  a == b = compare a b == EQ

isDisjoint :: RSTables -> RSTables -> Bool
isDisjoint s1 s2 =
    let
        t1 = Set.map t_name $ tables s1
        t2 = Set.map t_name $ tables s2
    in
        Set.fold (\ x y -> y && (x `Set.notMember` t2)) True t1 &&
        Set.fold (\ x y -> y && (x `Set.notMember` t1)) True t2
