{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

-}

{- 

TODO:
  - Signaturen anpassen, KL ..done
  - ATermConvertible analog show showList umbauen, KL ..done

  - ATermConvertible Instanzen, die zur Zeit auskommentiert sind, an
    das neue Interface der Klasse anpassen. Sowohl toATerm/fromATerm,
    als auch toShATerm/fromShATerm implementieren. Für Char eine neue
    einfügen, die analog zu 'ATermConvertible String' arbeitet, aber
    die neuen Funktionen toATermList/fromATermList
    bzw. toShATermList/fromShATermList implementiert. ..done

-}
module Common.ATerm.Conversion(
                      ATermConvertible,
		      toATerm,            -- :: t -> ATerm
		      fromATerm,          -- :: ATerm -> t
		      toATermList,        -- :: [t] -> ATerm
		      fromATermList,      -- :: ATerm -> [t]
		      toShATerm,          -- :: ATermTable -> t -> (ATermTable,Int)
		      fromShATerm,        -- :: ATermTable -> t
		      toShATermList,      -- :: ATermTable -> [t] -> (ATermTable,Int)
		      fromShATermList,    -- :: ATermTable -> [t]
                      toATermString,      -- :: ATermConvertible a => a -> String
		      fromATermString,    -- :: ATermConvertible a => String -> a
		      toSharedATermString,-- :: ATermConvertible a => a -> String
		      fromATermError,     -- :: String -> ATerm -> a
		      fromShATermError,   -- :: String -> ShATerm -> a
                      ) where

import Common.ATerm.AbstractSyntax
import Common.ATerm.ReadWrite
import List (mapAccumL)
import Data.Maybe
import Data.Ratio

class ATermConvertible t where
  -- ATerm  
    -- conversion functions known from Joost Visser
    toATerm   :: t -> ATerm
    fromATerm :: ATerm -> t
    -- conversion functions to omit overlapping instances
    toATermList   :: [t] -> ATerm
    fromATermList :: ATerm -> [t]

    -- default functions ignore the Annotation part
    toATermList ts = AList (map toATerm ts) []
    fromATermList aterm = 
	case aterm of
	AList aterms _ -> map fromATerm aterms
	_              -> fromATermError "[a]" aterm

  -- ShATerm
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

toATermString :: ATermConvertible a => a -> String
toATermString t	 = (writeATerm . fst) (toShATerm emptyATermTable t)

toSharedATermString :: ATermConvertible a => a -> String
toSharedATermString t = (writeSharedATerm . fst) (toShATerm emptyATermTable t)

fromATermString :: ATermConvertible a => String -> a
fromATermString s 	 = fromShATerm (readATerm s)

fromATermError :: String -> ATerm -> a
fromATermError t u = error ("Cannot convert ATerm to "++t++": "++(err u))
    where err te = case te of 
		  AAppl s _ _ -> "!AAppl "++s
		  AList _ _   -> "!AList"
		  _           -> "!AInt"

fromShATermError :: String -> ShATerm -> a
fromShATermError t u = error ("Cannot convert ShATerm to "++t++": "++(err u))
    where err te = case te of 
		  ShAAppl s l _ -> "!ShAAppl "++s 
				   ++ " ("++show (length l)++")"
		  ShAList l _   -> "!ShAList"
				   ++ " ("++show (length l)++")"
		  ShAInt i _    -> "!ShAInt " ++ show i


-- some instances -----------------------------------------------
instance ATermConvertible Bool where
    toATerm b = case b of
		 True  -> AAppl "true"  [] []
		 False -> AAppl "false" [] []
    fromATerm at = case at of 
		    AAppl "true"  [] _ -> True
		    AAppl "false" [] _ -> False
		    _                    -> fromATermError "Bool" at
    toShATerm att b = case b of
                       True  -> addATerm (ShAAppl "true" [] []) att 
                       False -> addATerm (ShAAppl "false" [] []) att
    fromShATerm att = case at of 
		       ShAAppl "true"  [] _ -> True
		       ShAAppl "false" [] _ -> False
		       _                     -> fromShATermError "Bool" at
                      where at = getATerm att
-- for Integer derive : ATermConvertible hand written!

instance ATermConvertible Integer where
    toATerm x    = AInt x []
    fromATerm at = case at of 
		    (AInt x _)  -> x
		    _           -> fromATermError "Integer" at
    toShATerm att x = addATerm (ShAInt x []) att
    fromShATerm att = case at of 
		       (ShAInt x _)  -> x
		       _             -> fromShATermError "Integer" at
                      where at = getATerm att

instance ATermConvertible Int where
    toATerm x    = AInt (toInteger x) [] 
    fromATerm at = case mi y of
		      (Just i) -> i
		      Nothing  -> error ("Integer to big for Int: "++(show y))
                   where
                   y::Integer 
                   y = fromATerm at
                 
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

instance (ATermConvertible a,Integral a) => ATermConvertible (Ratio a) where
   toATerm i =            let (i1, i2) = (numerator i, denominator i)
                              at1 = toATerm i1
                              at2 = toATerm i2
                          in AAppl "Ratio" [at1,at2] []
   fromATerm at = case at of
                   (AAppl "Ratio" [at1,at2] _) -> let i1 = fromATerm at1
						      i2 = fromATerm at2
						   in (i1 % i2)
		   _ -> fromATermError "Ratio" at
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

instance ATermConvertible Char where                   
   toATerm c = AAppl s [] []
               where 
               s = show (c:[]) 
   fromATerm at = case at of
		   (AAppl s [] _) -> conv s 
                   _              ->  fromATermError "Char" at
   toATermList s = AAppl (show s) [] []
   fromATermList at = case at of
                       (AAppl s [] _) -> read s      
                       _              -> fromATermError "String" at    

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
			
{-
conv :: String -> String
conv ('\"':sr) = case reverse sr of
                  ('\"':so) -> conv' (reverse so)
                               where
			       conv' [] = []
                               conv' ('\\':x:xs) = case x of
                                                    'n'  -> '\n' : conv' xs
		                                    't'  -> '\t' : conv' xs
		                                    'r'  -> '\r' : conv' xs
		                                    '\"' -> '\"' : conv' xs
                                                    _    -> x : conv' xs                     -- provisorisch  
		                                    _    -> error ("very strange reach:" ++ [x] ++":")
                               conv' (x:xs)      = x : conv' xs
                               conv' _           = error "String not convertible to char"
                  _         -> error "No matching '\"' found"
conv _         = error "String doesn't begin with '\"'"
-}
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
                               conv' (x:[])      = x
                               conv' _           = error "String not convertible to char"
                  _         -> error "No matching '\"' found"
conv _         = error "String doesn't begin with '\"'"

instance ATermConvertible () where
    toATerm _ = AAppl "UNIT" [] []
    fromATerm at = case at of
                    (AAppl "UNIT" [] _) -> ()
                    _               -> fromATermError "()" at
    toShATerm att _ = addATerm (ShAAppl "UNIT" [] []) att
    fromShATerm att = case at of
                       (ShAAppl "UNIT" [] _) -> ()
                       _                 -> fromShATermError "()" at
                      where at = getATerm att






