
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
import List (mapAccumL)
import qualified Common.Lib.Map as Map hiding (map)
import qualified Common.Lib.Set as Set 
import qualified Common.Lib.Rel as Rel
import Data.Maybe
import GHC.Real

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
   toATerm ((:%) i1 i2) = let at1 = toATerm i1
                              at2 = toATerm i2
                          in AAppl "Ratio" [at1,at2] []
   fromATerm at = case at of
                   (AAppl "Ration" [at1,at2] _) -> let i1 = fromATerm at1
						       i2 = fromATerm at2
						   in (i1 % i2)
		   _ -> fromATermError "Ratio" at
   toShATerm att0 ((:%) i1 i2) = 
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

instance (ATermConvertible a) => ATermConvertible (Maybe a) where
    toATerm mb = case mb of
                     Nothing -> (AAppl "Nothing" [] [])
                     (Just x)  -> let x' = toATerm x
                                  in (AAppl "Just" [x'] [])
    fromATerm at  = case at of
                     (AAppl "Nothing" [] _) -> Nothing
                     (AAppl "Just" [x] _) -> let x' = fromATerm x
					     in (Just x')
		     _ -> fromATermError "Maybe" at
    toShATerm att mb = case mb of
                     Nothing -> addATerm (ShAAppl "Nothing" [] []) att
                     (Just x)  -> case toShATerm att x of
				  (att1,x') ->
                                   addATerm (ShAAppl "Just" [x'] []) att1
    fromShATerm att = case aterm of
                       (ShAAppl "Nothing" [] _) -> Nothing
                       (ShAAppl "Just" [x] _) -> 
			   case fromShATerm (getATermByIndex1 x att) of
                           x' -> (Just x')
		       _      -> fromShATermError "Maybe" aterm
                      where aterm = getATerm att

instance (Ord a, ATermConvertible a, ATermConvertible b) => ATermConvertible (Map.Map a b) where
    toATerm fm       = let ml = toATerm (Map.toAscList fm)
		       in (AAppl "Map" [ml] [])
    fromATerm at     = case at of
		       (AAppl "Map" [ml] []) -> Map.fromDistinctAscList $ fromATerm ml
		       _ -> fromATermError "Map" at
    toShATerm att fm = case toShATerm att $ Map.toAscList fm of
		        (att1,i) ->
                          {-seq att1 $-} addATerm (ShAAppl "Map" [i] []) att1
    fromShATerm att  = case aterm of
		       (ShAAppl "Map" [i] []) -> 
			   case fromShATerm (getATermByIndex1 i att) of
			   l -> Map.fromDistinctAscList l
		       u     -> fromShATermError "Map" u
		       where aterm = getATerm att

instance (Ord a,ATermConvertible a) => ATermConvertible (Set.Set a) where
    toATerm set       = let ml = toATerm (Set.toAscList set)
		        in (AAppl "Set" [ml] [])
    fromATerm at     = case at of
		       (AAppl "Set" [ml] []) -> Set.fromDistinctAscList $ fromATerm ml
		       _ -> fromATermError "Set" at
    toShATerm att set = case  toShATerm att $ Set.toAscList set of
			 (att1,i) ->
                          {-seq att1 $-} addATerm (ShAAppl "Set" [i] []) att1
    fromShATerm att  = case aterm of
		       (ShAAppl "Set" [i] []) -> 
			   case fromShATerm (getATermByIndex1 i att) of
			   l -> Set.fromDistinctAscList l
		       u     -> fromShATermError "Set" u
		       where aterm = getATerm att

instance (Ord a,ATermConvertible a) => ATermConvertible (Rel.Rel a) where
    toATerm rel       = let ml = toATerm (Rel.toList rel)
		        in (AAppl "Rel" [ml] [])
    fromATerm at     = case at of
		       (AAppl "Rel" [ml] []) -> Rel.fromList $ fromATerm ml
		       _ -> fromATermError "Rel" at
    toShATerm att set = case toShATerm att $ Rel.toList set of
                        (att1,i) -> 
			 {-seq att1 $-} addATerm (ShAAppl "Rel" [i] []) att1
    fromShATerm att  = case aterm of
		       (ShAAppl "Rel" [i] []) -> 
			   case fromShATerm (getATermByIndex1 i att) of
			   l -> Rel.fromList l
		       u     -> fromShATermError "Rel" u
		       where aterm = getATerm att

{-    toATerm set = case set of
                   (Tip) -> AAppl "Tip" [] []
                   (Bin i a set1 set2) -> let aa = toATerm i
                                              bb = toATerm a
					      cc = toATerm set1
                                              dd = toATerm set2
                                             in AAppl "Bin" [aa,bb,cc,dd] []
    fromATerm at = case at of
                    (AAppl "Tip" [] _) -> Tip
                    (AAppl "Bin" [aa,bb,cc,dd] _) -> let aa' = fromATerm aa
                                                         bb' = fromATerm bb
						         cc' = fromATerm cc
						     in (Bin aa' bb' cc' dd')
    toShATerm att at = case at of
                        (Tip) -> addATerm (ShAAppl "Tip" [] []) att
                        (Bin i a set1 set2) -> let (att1,i') = toShATerm att i
                                                   (att2,a') = toShATerm att1 a
                                                   (att3,set1') = toShATerm att2 set1
                                                   (att4,set2') = toShATerm att3 set2
                                               in addATerm (ShAAppl "Bin" [i',a',set1',set2'] []) att4
                        _                   -> toShATermError "Set" at
    fromShATerm att = case aterm of
                       (ShAAppl "Tip" [] _) -> Tip
                       (ShAAppl "Bin" [aa,bb,cc,dd] _) -> 
                         let aa' = fromShATerm (getATermByIndex1 aa att)
		             bb' = fromShATerm (getATermByIndex1 bb att)
		             cc' = fromShATerm (getATermByIndex1 cc att)
		             dd' = fromShATerm (getATermByIndex1 dd att) 
                         in (Bin aa' bb' cc' dd')
                       _ -> fromShATermError "Set" aterm
                      where aterm = getATerm att
-}
instance ATermConvertible a => ATermConvertible [a] where
    toATerm l        = toATermList l
    fromATerm at     = fromATermList at
    toShATerm att l  = toShATermList att l 
    fromShATerm att  = fromShATermList att

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

instance (ATermConvertible a,ATermConvertible b) => ATermConvertible (a,b) where
    toATerm (a,b)    = AAppl "" [toATerm a,toATerm b] []
    fromATerm at     = case at of
                        (AAppl "" [a,b] _) -> (fromATerm a,fromATerm b)
                        _                  -> fromATermError "(a,b)" at
    toShATerm att0 (x,y) = case toShATerm att0 x of
			   (att1,x') -> 
			     case toShATerm att1 y of
			     (att2,y') -> 
                               addATerm (ShAAppl "" [x',y'] []) att2
    fromShATerm att = case at of  
                       (ShAAppl "" [x,y] _) -> 
			case fromShATerm (getATermByIndex1 x att) of
			x' -> 
			 case fromShATerm (getATermByIndex1 y att) of
			 y' -> (x',y')
                       _  -> fromShATermError "(a,b)" at
                      where at = getATerm att 

instance (ATermConvertible a, ATermConvertible b, ATermConvertible c) => ATermConvertible (a,b,c) where
    toATerm (a,b,c) = AAppl "" [toATerm a, toATerm b, toATerm c] []
    fromATerm at    = case at of
                       (AAppl "" [a,b,c] _) -> (fromATerm a, fromATerm b, fromATerm c)
                       _                          -> fromATermError "(a,b,c)" at
    toShATerm att0 (a,b,c) = case toShATerm att0 a of
			     (att1,x') -> 
			      case toShATerm att1 b of
			      (att2,y') -> 
                               case toShATerm att2 c of
			       (att3,z') -> 
				  addATerm (ShAAppl "" [x',y',z'] []) att3 
    fromShATerm att = case at of 
		       (ShAAppl "" [a,b,c] _) -> 
			case fromShATerm (getATermByIndex1 a att) of
			a' -> 
			 case fromShATerm (getATermByIndex1 b att) of
			 b' ->
			  case fromShATerm (getATermByIndex1 c att) of
			  c' -> (a',b',c')			     
                       _                 -> fromShATermError "(a,b,c)" at
                      where at = getATerm att
                            
instance (ATermConvertible a, ATermConvertible b, ATermConvertible c, ATermConvertible d) => ATermConvertible (a,b,c,d) where
    toATerm (a,b,c,d) = AAppl "" [toATerm a, toATerm b, toATerm c,toATerm d] []
    fromATerm at    = case at of
                       (AAppl "" [a,b,c,d] _) -> (fromATerm a, fromATerm b, fromATerm c, fromATerm d)
                       _                          -> fromATermError "(a,b,c)" at
    toShATerm att0 (a,b,c,d) = 
	case toShATerm att0 a of
        (att1,a') -> 
	    case toShATerm att1 b of
	    (att2,b') -> 
                case toShATerm att2 c of
		(att3,c') -> 
		    case toShATerm att3 d of
		    (att4,d') -> 
			addATerm (ShAAppl "" [a',b',c',d'] []) att4 
    fromShATerm att = 
	case at of 
        (ShAAppl "" [a,b,c,d] _) ->
 	 case fromShATerm (getATermByIndex1 a att) of
	 a' -> 
	  case fromShATerm (getATermByIndex1 b att) of
	  b' ->
	   case fromShATerm (getATermByIndex1 c att) of
	   c' -> 
	    case fromShATerm (getATermByIndex1 d att) of
	    d' -> (a',b',c',d')
        _                            -> fromShATermError "(a,b,c)" at
      where at = getATerm att






