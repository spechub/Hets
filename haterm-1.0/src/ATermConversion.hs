{-# OPTIONS -fallow-overlapping-instances #-}
module ATermConversion where

import ATermAbstractSyntax
import ATermReadWrite
import List (find,mapAccumL)

class ATermConvertible t where
  toATerm   :: ATermTable -> t -> (ATermTable,ATerm)
  toATerm1  :: ATermTable -> t -> ATermTable
  toATerm1 at t = let (at',_) = toATerm at t in at' 
  fromATerm :: ATermTable -> t
  

toATermString at t	 = writeATerm       (toATerm1 at t)
toSharedATermString at t = writeSharedATerm (toATerm1 at t)
fromATermString s 	 = fromATerm (readATerm s)

toATermString1 t         = writeATerm (toATerm1 emptyATermTable t)
toSharedATermString1 t   = writeSharedATerm (toATerm1 emptyATermTable t)

fromATermError t u = error ("Cannot convert ATerm to "++t++": "++(err u))
    where err u = case u of 
		  AAppl s _ -> "!AAppl "++s
		  AList _   -> "!AList"
		  otherwise -> "!AInt"

{- for Integer derive : ATermConvertible hand written!-}

instance ATermConvertible Integer where
    toATerm at x        = addATerm (AInt x) at
    fromATerm at = case aterm of 
		   (AInt x)  -> x
		   otherwise -> fromATermError "Integer" aterm
	where aterm = getATerm at

instance ATermConvertible Int where
    toATerm at x    = toATerm at (toInteger x)
    fromATerm at    = case mi of
		      (Just i) -> i
		      Nothing  -> error ("Integer to big for Int: "++(show x))
	where mi = if toInteger ((fromInteger::Integer->Int) x) == x then 
			      Just (fromInteger x)
	           else       Nothing 
	      x::Integer = fromATerm at

instance ATermConvertible String where
    toATerm at s      = addATerm (AAppl s' []) at
	where s'  = concat ["\"",s'',"\""]
	      s'' = concatMap conv s
	      conv x | x `elem` "\n\\\t\"\r" = '\\':[x]
	      conv x | (fromEnum x) < 32     = 
			 error ('\"':x:'\"':" is not convertible") 
	      conv x    = [x]
    fromATerm at = case aterm of
		   (AAppl s []) -> conv s'
		       where s' = case s of
				  ('\"':so) -> case reverse so of
					       ('\"':sr) -> reverse sr
					       _         -> err
				  _         -> err
			     conv ""          = ""
			     conv ('\\':x:xs) = 
				 if x `elem` "\n\\\t\"\r" then x:(conv xs)
				 else err
			     conv (x:xs)      = x:(conv xs)
		   otherwise    -> err 
	where aterm = getATerm at
	      err   = fromATermError "String" aterm

instance ATermConvertible a => ATermConvertible [a] where
    toATerm at l       = addATerm (AList l') at'
	where (at',l') = List.mapAccumL toATerm at l
    fromATerm at = case aterm of
		   (AList l) -> map conv l
		   otherwise -> fromATermError "[a]" aterm
	where aterm  = getATerm at
	      conv t = fromATerm (getATermByIndexSp1 t at)

instance (ATermConvertible a,ATermConvertible b) => ATermConvertible (a,b) 
    where
    toATerm at (x,y) = addATerm (AAppl "tuple" [x',y']) at'
	where (at' ,y') = toATerm at'' y
	      (at'',x') = toATerm at   x
    fromATerm at = case aterm of 
		   (AAppl "tuple" [x,y]) -> (x',y')
		       where x' = fromATerm (getATermByIndexSp1 x at)
			     y' = fromATerm (getATermByIndexSp1 y at)
		   otherwise             -> fromATermError "(a,b)" aterm
	where aterm = getATerm at 

--- some helpers needed and used by DrIFT instances ---------------------------
-- throws an error in case that there is no ATerm in the list
findATerm :: [Maybe ATerm] -> ATerm 
findATerm l = case List.find just l of
				    (Just(Just t)) -> t
				    otherwise      -> error "No aterm found"
    where just mt = case mt of
		    (Just _) -> True
		    Nothing  -> False
-------------------------------------------------------------------------------