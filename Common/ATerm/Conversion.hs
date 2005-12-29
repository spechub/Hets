{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

the class ShATermConvertible and a few instances
-}

module Common.ATerm.Conversion(
       ShATermConvertible,
       toShATerm,          -- :: ATermTable -> t -> (ATermTable,Int)
       fromShATerm,        -- :: ATermTable -> t
       toShATermList,      -- :: ATermTable -> [t] -> (ATermTable,Int)
       fromShATermList,    -- :: ATermTable -> [t]
       type_of,            -- :: t -> String
       fromShATermError,   -- :: String -> ShATerm -> a
                              ) where

import Common.ATerm.AbstractSyntax
import Data.List (mapAccumL)
import Data.Ratio

class ShATermConvertible t where
    -- functions for conversion to an ATermTable
    toShATerm       :: ATermTable -> t -> (ATermTable,Int)
    toShATermList   :: ATermTable -> [t] -> (ATermTable,Int)
    fromShATerm     :: ATermTable -> t
    fromShATermList :: ATermTable -> [t]
    type_of :: t -> String -- ^ deriving Typeable is more complicated

    -- default functions ignore the Annotation part
    toShATermList att0 ts = case mapAccumL toShATerm att0 ts of
                          (att1, inds) -> addATerm (ShAList inds []) att1

    fromShATermList att =
        case getATerm att of
            ShAList ats _ ->
                map (\ i -> fromShATerm (getATermByIndex1 i att)) ats
            u -> fromShATermError "[a]" u

fromShATermError :: String -> ShATerm -> a
fromShATermError t u = error $ "Cannot convert ShATerm to "
                       ++ t ++ ": " ++ err u
    where err te = case te of
                  ShAAppl s l _ -> "!ShAAppl "++ s
                                   ++ " (" ++ show (length l) ++ ")"
                  ShAList l _   -> "!ShAList"
                                   ++ " (" ++ show (length l) ++ ")"
                  ShAInt i _    -> "!ShAInt " ++ show i

-- some instances -----------------------------------------------
instance ShATermConvertible Bool where
    toShATerm att b = case b of
                       True  -> addATerm (ShAAppl "T" [] []) att
                       False -> addATerm (ShAAppl "F" [] []) att
    fromShATerm att = case getATerm att of
                       ShAAppl "T" [] _ -> True
                       ShAAppl "F" [] _ -> False
                       u -> fromShATermError "Prelude.Bool" u
    type_of _ = "Prelude.Bool"

instance ShATermConvertible Integer where
    toShATerm att x = addATerm (ShAInt x []) att
    fromShATerm att = case getATerm att of
                       ShAInt x _ -> x
                       u  -> fromShATermError "Prelude.Integer" u
    type_of _ = "Prelude.Integer"

instance ShATermConvertible Int where
    toShATerm att x = toShATerm att (toInteger x)
    fromShATerm att = integer2Int $ fromShATerm att
    type_of _ = "Prelude.Int"

instance (ShATermConvertible a, Integral a)
    => ShATermConvertible (Ratio a) where
    toShATerm att0 i = let (i1, i2) = (numerator i, denominator i) in
       case toShATerm att0 i1 of
       (att1,i1') ->
          case toShATerm att1 i2 of
          (att2,i2') ->
              addATerm (ShAAppl "Ratio" [i1',i2'] []) att2
    fromShATerm att =
       case getATerm att of
       ShAAppl "Ratio" [i1',i2'] _ ->
           case fromShATerm (getATermByIndex1 i1' att) of
           i1 ->
             case fromShATerm (getATermByIndex1 i2' att) of
             i2 -> (i1 % i2)
       u ->  fromShATermError "Prelude.Integral" u
    type_of _ = "Prelude.Integral"

instance ShATermConvertible Char where
    toShATerm att c = addATerm (ShAAppl (show [c]) [] []) att
    fromShATerm att = case getATerm att of
                        ShAAppl s [] _ -> str2Char s
                        u -> fromShATermError "Char" u
    toShATermList att s = addATerm (ShAAppl (show s) [] []) att
    fromShATermList att = case getATerm att of
                            ShAAppl s [] _ -> read s
                            u -> fromShATermError "String" u
    type_of _ = "Prelude.Char"

instance ShATermConvertible () where
    toShATerm att _ = addATerm (ShAAppl "U" [] []) att
    fromShATerm att = case getATerm att of
                      ShAAppl "U" [] _ -> ()
                      u -> fromShATermError "()" u
    type_of _ = "()"
