
{- HetCATS/Common/Id.hs
   $Id$
   Authors: Klaus Lüttich
            Christian Maeder
   Year:    2002

   This module supplies simple and mixfix identifiers. 
   A simple identifier is a lexical token given by a string and a start position.
   The ordering of tokens ignores position information.

   A place within mixfix identifiers is also a token.

   Mixfix identifiers may also have a compound list. 
   This compound list follows the last non-place token! 
-}

module Common.Id where

import Data.Char
import Common.Lib.Parsec.Pos 

-- identifiers, fixed for all logics

type Pos = SourcePos

nullPos :: Pos 
nullPos = newPos "" 0 0 

headPos :: [Pos] -> Pos 
headPos l = if null l then nullPos else head l

-- tokens as supplied by the scanner
data Token = Token { tokStr :: String
		   , tokPos :: Pos
		   } deriving (Show)

showTok :: Token -> ShowS
showTok = showString . tokStr

instance Eq Token where
   Token s1 _ == Token s2 _ = s1 == s2
 
instance Ord Token where
   Token s1 _  <= Token s2 _ = s1 <= s2

-- shortcut to get [Pos]
toPos :: Token -> [Token] -> Token -> [Pos]
toPos o l c = map tokPos (o:l++[c])

showSepList :: ShowS -> (a -> ShowS) -> [a] -> ShowS
showSepList _ _ [] = id
showSepList _ f [x] = f x
showSepList s f (x:r) = f x . s . showSepList s f r

-- special token
place :: String
place = "__"

isPlace :: Token -> Bool
isPlace (Token t _) = t == place
 
-- an identifier may be mixfix (though not for a sort) and compound
-- TokenOrPlace list must be non-empty!
data Id = Id [Token] [Id] [Pos] 
                                 -- pos of "[", commas, "]" 
	  deriving (Show)
-- for pretty printing see PrettyPrint.hs

instance Eq Id where
    Id tops1 ids1 _ == Id tops2 ids2 _ = (tops1, ids1) == (tops2, ids2)

instance Ord Id where
    Id tops1 ids1 _ <= Id tops2 ids2 _ = (tops1, ids1) <= (tops2, ids2)

noShow :: Bool -> ShowS -> ShowS
noShow b s = if b then id else s

showIds :: [Id] -> ShowS
showIds is = noShow (null is) $ showString "[" 
	     . showSepList (showString ",") showId is
	     . showString "]"

showId :: Id -> ShowS
showId (Id ts is _) = 
	let (toks, places) = splitMixToken ts 
	    showToks = showSepList id showTok
	in  showToks toks . showIds is . showToks places

splitMixToken :: [Token] -> ([Token],[Token])
splitMixToken l = let (pls, toks) = span isPlace (reverse l) in
	      (reverse toks, reverse pls)

-- prefix ids do not need to be followed by places in HasCASL
stripFinalPlaces :: Id -> Id
stripFinalPlaces (Id ts cs ps) =
    Id (fst $ splitMixToken ts) cs ps 

-- reconstruct token list 
-- expandPos f ("{", "}") [a,b] [(1,1), (1,3), 1,5)] = 
-- [ t"{" , a , t"," , b , t"}" ] where t = f . Token (and proper positions)
expandPos :: (Token -> a) -> (String, String) -> [a] -> [Pos] -> [a]
expandPos f (o, c) ts ps =
    if null ts then if null ps then map (f . mkSimpleId) [o, c]
       else map f (zipWith Token [o, c] [head ps , last ps])
    else  let n = length ts + 1
              diff = n - length ps
	      ps1 = if diff > 0 then ps ++ replicate diff nullPos
		    -- pad with nullPos
		    else take n $ drop (- diff `div` 2) ps
		    -- cut off longer lists on both ends
	      seps = map f
		(zipWith Token (o : replicate (n - 2) "," ++ [c]) ps1)
	  in head seps : concat (zipWith (\ t s -> [t,s]) ts (tail seps))
	    		    
-- all tokens including "," within compound lists as sequence
-- either generate literal places or the non-terminal termTok
getTokenList :: String -> Id -> [Token]
getTokenList placeStr (Id ts cs ps) = 
    let (toks, pls) = splitMixToken ts 
        cts = if null cs then [] else concat 
	      $ expandPos (:[]) ("[", "]") (map (getTokenList place) cs) ps
	      -- although positions will be replaced (by scan)
        convert = if placeStr == place then id else 
		  map (\ t -> if isPlace t then t {tokStr = placeStr} else t) 
    in convert toks ++ cts ++ convert pls

-- compute a meaningful single position for diagnostics

posOfId :: Id -> Pos
posOfId (Id [] _ _) = error "Id.posOfId"
posOfId (Id ts _ _) = let l = dropWhile isPlace ts 
		      in if null l then -- for invisible "__ __" (only places)
			   tokPos $ last ts
			 else tokPos $ head l

-- Simple Ids

type SIMPLE_ID = Token
mkSimpleId :: String -> Token
mkSimpleId s = Token s nullPos

simpleIdToId :: SIMPLE_ID -> Id
simpleIdToId sid = Id [sid] [] []

---- some useful predicates for Ids -------------------------------------
isOrdAppl :: Id -> Bool
isOrdAppl = not . isMixfix

isMixfix :: Id -> Bool
isMixfix (Id tops _ _) = any isPlace tops 

isPrefix :: Id -> Bool
isPrefix (Id tops _ _) =    (not . isPlace . head) tops 
			 && (isPlace . last)       tops 

isPostfix :: Id -> Bool
isPostfix (Id tops _ _) =    (isPlace . head)       tops 
			  && (not . isPlace . last) tops 

isInfix2 :: Id -> Bool
isInfix2 (Id tops _ _)
    | length tops == 3 =    (isPlace . head) tops 
			 && (isPlace . last) tops
			 && (not . isPlace . head . tail) tops
    | otherwise = False

isInfix :: Id -> Bool
isInfix (Id tops _ _) =    (isPlace . head) tops 
			&& (isPlace . last) tops

isSurround :: Id -> Bool
isSurround i@(Id tops _ _) =    (not . isPlace . head) tops 
			     && (not . isPlace . last) tops
			     && (isMixfix i)

isCompound :: Id -> Bool
isCompound (Id _ cs _) = not $ null cs

---- helper class -------------------------------------------------------

{- This class is derivable with DrIFT in HetCATS/utils ! 
   
   It's main purpose is to have an function that "works" on every
   constructor with a Pos or [Pos] field. During parsing, mixfix
   analysis and ATermConversion this function might be very useful.

-}
class PosItem a where
    up_pos    :: (Pos -> Pos)    -> a -> a
    up_pos_l  :: ([Pos] -> [Pos]) -> a -> a
    get_pos   :: a -> Maybe Pos
    get_pos_l :: a -> Maybe [Pos]
    up_pos_err  :: String -> a
    up_pos_err fn = 
	error ("function \"" ++ fn ++ "\" is not implemented")
    up_pos _    = id
    up_pos_l _  = id
    get_pos   _ = Nothing
    get_pos_l _ = Nothing
    
-------------------------------------------------------------------------

-- Two fine instances, DrIFTed but handcopied and extended
instance PosItem Token where
    up_pos fn1 (Token aa ab) = (Token aa (fn1 ab))
    get_pos (Token _ ab) = Just ab

instance PosItem Id where
    up_pos_l fn1 (Id aa ab ac) = (Id aa ab (fn1 ac))
    get_pos_l (Id _ _ ac) = Just ac
    get_pos = Just . posOfId
