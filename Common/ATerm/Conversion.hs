{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

-}

module Common.ATerm.Conversion(
       ShATermConvertible,
       toShATerm,          -- :: ATermTable -> t -> (ATermTable,Int)
       fromShATerm,        -- :: ATermTable -> t
       toShATermList,      -- :: ATermTable -> [t] -> (ATermTable,Int)
       fromShATermList,    -- :: ATermTable -> [t]
       fromShATermError,   -- :: String -> ShATerm -> a
                              ) where

import Common.ATerm.AbstractSyntax
import Data.List (mapAccumL)
import Data.Maybe
import Data.Ratio

class ShATermConvertible t where
    -- functions for conversion to an ATermTable
    toShATerm       :: ATermTable -> t -> (ATermTable,Int)  
    toShATermList   :: ATermTable -> [t] -> (ATermTable,Int)  
    fromShATerm     :: ATermTable -> t
    fromShATermList :: ATermTable -> [t]

    -- default functions ignore the Annotation part
    toShATermList at ts = case mapAccumL toShATerm at ts of
                          (at',inds) -> addATerm (ShAList inds []) at'

    fromShATermList at = 
        case getATerm at of
        aterm -> 
            case aterm of 
            ShAList ats _ ->  
                map (\i -> fromShATerm (getATermByIndex1 i at)) ats
            _           -> fromShATermError "[a]" aterm

fromShATermError :: String -> ShATerm -> a
fromShATermError t u = error ("Cannot convert ShATerm to "++t++": "++(err u))
    where err te = case te of 
                  ShAAppl s l _ -> "!ShAAppl "++s 
                                   ++ " ("++show (length l)++")"
                  ShAList l _   -> "!ShAList"
                                   ++ " ("++show (length l)++")"
                  ShAInt i _    -> "!ShAInt " ++ show i


-- some instances -----------------------------------------------
instance ShATermConvertible Bool where
    toShATerm att b = case b of
                       True  -> addATerm (ShAAppl "true" [] []) att 
                       False -> addATerm (ShAAppl "false" [] []) att
    fromShATerm att = case at of 
                       ShAAppl "true"  [] _ -> True
                       ShAAppl "false" [] _ -> False
                       _                     -> fromShATermError "Bool" at
                      where at = getATerm att
-- for Integer derive : ShATermConvertible hand written!

instance ShATermConvertible Integer where
    toShATerm att x = addATerm (ShAInt x []) att
    fromShATerm att = case at of 
                       (ShAInt x _)  -> x
                       _             -> fromShATermError "Integer" at
                      where at = getATerm att

instance ShATermConvertible Int where
    toShATerm att x = toShATerm att (toInteger x)
    fromShATerm att = case mi y of
                       (Just i) -> i
                       Nothing  -> error ("Integer to big for Int: "++(show y))
                      where
                      y::Integer 
                      y = fromShATerm att

mi :: (Num a) => Integer -> Maybe a
mi x = if toInteger ((fromInteger::Integer->Int) x) == x 
                  then Just (fromInteger x) 
                  else Nothing                     

instance (ShATermConvertible a, Integral a) 
    => ShATermConvertible (Ratio a) where
   toShATerm att0 i = let (i1, i2) = (numerator i, denominator i) in
       case toShATerm att0 i1 of
       (att1,i1') -> 
          case toShATerm att1 i2 of
          (att2,i2') ->
              addATerm (ShAAppl "Ratio" [i1',i2'] []) att2
   fromShATerm att = 
       case aterm of
       (ShAAppl "Ratio" [i1',i2'] _) -> 
           case fromShATerm (getATermByIndex1 i1' att) of
           i1 -> 
             case fromShATerm (getATermByIndex1 i2' att) of
             i2 -> (i1 % i2)
       _                ->  fromShATermError "Ratio" aterm
       where aterm = getATerm att 

instance ShATermConvertible Char where                   
   toShATerm att c = addATerm (ShAAppl (show (c:[])) [] []) att 
   fromShATerm att = case at of
                      (ShAAppl s [] _) -> conv s
                      _                ->  fromShATermError "Char" at
                      where at = getATerm att 
   toShATermList att s = addATerm (ShAAppl (show s) [] []) att
   fromShATermList att = case at of 
                         (ShAAppl s [] _) -> read s
                         _                -> fromShATermError "String" at
                       where at = getATerm att
                        
conv :: String -> Char
conv ('\"':sr) = case reverse sr of
                  ('\"':so) -> conv' (reverse so)
                               where
                               conv' ('\\':x:[]) = case x of
                                   'n'  -> '\n'
                                   't'  -> '\t'
                                   'r'  -> '\r'
                                   '\"' -> '\"'
                                   _    -> error "very strange reach"
                               conv' (x:[]) = x
                               conv' _ = error "String not convertible to char"
                  _         -> error "No matching '\"' found"
conv _         = error "String doesn't begin with '\"'"

instance ShATermConvertible () where
    toShATerm att _ = addATerm (ShAAppl "UNIT" [] []) att
    fromShATerm att = case at of
                       (ShAAppl "UNIT" [] _) -> ()
                       _                 -> fromShATermError "()" at
                      where at = getATerm att
