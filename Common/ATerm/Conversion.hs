
{-# OPTIONS -fallow-overlapping-instances #-}

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
import List (find,mapAccumL)
import Common.Lib.Map hiding (map)

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
    toShATermList at ts = addATerm (ShAList inds []) at'
	where (at',inds) = mapAccumL toShATerm at ts
    fromShATermList at = 
	case aterm of 
	ShAList ats _ ->  map conv ats
	_           -> fromShATermError "[a]" aterm
	where aterm  = getATerm at
	      conv i = fromShATerm (getATermByIndex1 i at)


toATermString :: ATermConvertible a => a -> String
toATermString t	 = (writeATerm . fst) (toShATerm emptyATermTable t)

toSharedATermString :: ATermConvertible a => a -> String
toSharedATermString t = (writeSharedATerm . fst) (toShATerm emptyATermTable t)

fromATermString :: ATermConvertible a => String -> a
fromATermString s 	 = fromShATerm (readATerm s)

fromATermError :: String -> ATerm -> a
fromATermError t u = error ("Cannot convert ATerm to "++t++": "++(err u))
    where err u = case u of 
		  AAppl s _ _ -> "!AAppl "++s
		  AList _ _   -> "!AList"
		  _           -> "!AInt"

fromShATermError :: String -> ShATerm -> a
fromShATermError t u = error ("Cannot convert ShATerm to "++t++": "++(err u))
    where err u = case u of 
		  ShAAppl s _ _ -> "!ShAAppl "++s
		  ShAList _ _   -> "!ShAList"
		  _             -> "!ShAInt"


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
              
instance (Ord a, ATermConvertible a, ATermConvertible b) => ATermConvertible (Map a b) where
    toATerm fm       = toATerm (toList fm)
    fromATerm at     = fromList $ fromATerm at
    toShATerm att fm = toShATerm att $ toList fm 
    fromShATerm att  = fromList $ fromShATerm att

instance ATermConvertible a => ATermConvertible [a] where
    toATerm l        = toATermList l
    fromATerm at     = fromATermList at
    toShATerm att l  = toShATermList att l 
    fromShATerm att  = fromShATermList att

instance (ATermConvertible a,ATermConvertible b) => ATermConvertible (a,b) where
    toATerm (a,b)    = AAppl "" [toATerm a,toATerm b] []
    fromATerm at     = case at of
                        (AAppl "" [a,b] _) -> (fromATerm a,fromATerm b)
                        _                  -> fromATermError "(a,b)" at
    toShATerm att (x,y) = addATerm (ShAAppl "" [x',y'] []) att' 
                          where (att' ,y') = toShATerm att'' y 
                                (att'',x') = toShATerm att   x 
    fromShATerm att = case at of  
                       (ShAAppl "" [x,y] _) -> (x',y')
                        where x' = fromShATerm (getATermByIndex1 x att) 
                              y' = fromShATerm (getATermByIndex1 y att) 
                       _  -> fromShATermError "(a,b)" at
                      where at = getATerm att 

instance (ATermConvertible a, ATermConvertible b, ATermConvertible c) => ATermConvertible (a,b,c) where
    toATerm (a,b,c) = AAppl "" [toATerm a, toATerm b, toATerm c] []
    fromATerm at    = case at of
                       (AAppl "" [a,b,c] _) -> (fromATerm a, fromATerm b, fromATerm c)
                       _                          -> fromATermError "(a,b,c)" at
    toShATerm att (a,b,c) = addATerm (ShAAppl "" [a',b',c'] []) att1 
                            where (att1,c')  = toShATerm att'' c
			          (att'',b') = toShATerm att'  b 
                                  (att',a')  = toShATerm att   a
    fromShATerm att = case at of 
		       (ShAAppl "" [a,b,c] _) -> (a',b',c')
                         where a' = fromShATerm (getATermByIndex1 a att) 
                               b' = fromShATerm (getATermByIndex1 b att) 
			       c' = fromShATerm (getATermByIndex1 c att) 
			     
                       _                            -> fromShATermError "(a,b,c)" at
                      where at = getATerm att
                            
instance (ATermConvertible a, ATermConvertible b, ATermConvertible c, ATermConvertible d) => ATermConvertible (a,b,c,d) where
    toATerm (a,b,c,d) = AAppl "" [toATerm a, toATerm b, toATerm c,toATerm d] []
    fromATerm at    = case at of
                       (AAppl "" [a,b,c,d] _) -> (fromATerm a, fromATerm b, fromATerm c, fromATerm d)
                       _                          -> fromATermError "(a,b,c)" at
    toShATerm att (a,b,c,d) = addATerm (ShAAppl "" [a',b',c',d'] []) att2 
                              where (att2,d')  = toShATerm att1  d
                                    (att1,c')  = toShATerm att'' c
			            (att'',b') = toShATerm att'  b 
                                    (att',a')  = toShATerm att   a
    fromShATerm att = case at of 
		       (ShAAppl "" [a,b,c,d] _) -> (a',b',c',d')
                         where a' = fromShATerm (getATermByIndex1 a att) 
                               b' = fromShATerm (getATermByIndex1 b att) 
			       c' = fromShATerm (getATermByIndex1 c att) 
			       d' = fromShATerm (getATermByIndex1 d att)
                       _                            -> fromShATermError "(a,b,c)" at
                      where at = getATerm att






