{- |

Module      :  $Header$
Copyright   :  (c) Klaus Lüttich and Christian Maeder and Uni Bremen 2002-2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable


This modul supplies simple and mixfix identifiers. 
A simple identifier is a lexical token given by a string and a start position.

-  A 'place' is a special token within mixfix identifiers.

-  A mixfix identifier may have a compound list. 
   This compound list follows the last non-place token! 
-}

module Common.Id where

import Data.Char
import Common.Lib.Parsec.Pos 

-- identifiers, fixed for all logics

type Pos = SourcePos

-- | unknown position
nullPos :: Pos 
nullPos = newPos "" 0 0 

-- | first 'Pos' or 'nullPos'
headPos :: [Pos] -> Pos 
headPos l = if null l then nullPos else head l

-- | tokens as supplied by the scanner
data Token = Token { tokStr :: String
		   , tokPos :: Pos
		   } deriving (Show)

-- | show the plain string
showTok :: Token -> ShowS
showTok = showString . tokStr

-- | ignore 'tokPos'
instance Eq Token where
   Token s1 _ == Token s2 _ = s1 == s2
 
-- | ignore 'tokPos'
instance Ord Token where
   Token s1 _  <= Token s2 _ = s1 <= s2

-- | shortcut to get positions of surrounding and interspersed tokens
toPos :: Token -> [Token] -> Token -> [Pos]
toPos o l c = map tokPos (o:l++[c])

-- | intersperse seperators
showSepList :: ShowS -> (a -> ShowS) -> [a] -> ShowS
showSepList _ _ [] = id
showSepList _ f [x] = f x
showSepList s f (x:r) = f x . s . showSepList s f r

-- | the special 'place'
place :: String
place = "__"

-- | is a 'place' token
isPlace :: Token -> Bool
isPlace (Token t _) = t == place
 
-- | mixfix and compound identifiers
data Id = Id [Token] [Id] [Pos] 
          -- pos of square brackets and commas of a compound list
	  deriving (Show)

-- for pretty printing see PrettyPrint.hs

-- | ignore positions
instance Eq Id where
    Id tops1 ids1 _ == Id tops2 ids2 _ = (tops1, ids1) == (tops2, ids2)

-- | ignore positions
instance Ord Id where
    Id tops1 ids1 _ <= Id tops2 ids2 _ = (tops1, ids1) <= (tops2, ids2)

-- | shortcut to suppress output for input condition
noShow :: Bool -> ShowS -> ShowS
noShow b s = if b then id else s

-- | shows a compound list 
showIds :: [Id] -> ShowS
showIds is = noShow (null is) $ showString "[" 
	     . showSepList (showString ",") showId is
	     . showString "]"

-- | shows an 'Id', puts final places behind a compound list
showId :: Id -> ShowS
showId (Id ts is _) = 
	let (toks, places) = splitMixToken ts 
	    showToks = showSepList id showTok
	in  showToks toks . showIds is . showToks places

-- | splits off the front and final places 
splitMixToken :: [Token] -> ([Token],[Token])
splitMixToken [] = ([], [])
splitMixToken (h:l) = 
    let (toks, pls) = splitMixToken l
	in if isPlace h && null toks 
	   then (toks, h:pls) 
	   else (h:toks, pls)

-- | ignores final places in an 'Id' (for HasCASL)
stripFinalPlaces :: Id -> Id
stripFinalPlaces (Id ts cs ps) =
    Id (fst $ splitMixToken ts) cs ps 

-- | return open and closing list bracket and a compound list
-- from a bracket 'Id'  (parsed by 'caslListBrackets')
getListBrackets :: Id -> ([Token], [Token], [Id])
getListBrackets (Id b cs _) = 
    let (b1, rest) = break isPlace b
	b2 = if null rest then [] 
	     else filter (not . isPlace) rest
    in (b1, b2, cs)

-- | reconstruct a list with surrounding strings and interspersed commas 
-- with proper position information 
-- that should be preserved by the input function
expandPos :: (Token -> a) -> (String, String) -> [a] -> [Pos] -> [a]
-- expandPos f ("{", "}") [a,b] [(1,1), (1,3), 1,5)] = 
-- [ t"{" , a , t"," , b , t"}" ] where t = f . Token (and proper positions)
expandPos f (o, c) ts ps =
    if null ts then if null ps then map (f . mkSimpleId) [o, c]
       else map f (zipWith Token [o, c] [head ps , last ps])
    else  let n = length ts + 1
              diff = n - length ps
	      ps1 = if diff > 0 then ps ++ replicate diff nullPos
		    -- pad with nullPos
		    else if diff == 0 then ps
			 else take n $ drop (- diff `div` 2) ps
		    -- cut off longer lists on both ends
	      commas j = if j == 2 then [c] else "," : commas (j - 1)
	      seps = map f
		(zipWith Token (o : commas n) ps1)
	  in head seps : concat (zipWith (\ t s -> [t,s]) ts (tail seps))
	    		    

-- | reconstruct the token list of an 'Id'
-- including square brackets and commas of (nested) compound lists.
getPlainTokenList :: Id -> [Token]
getPlainTokenList (Id ts cs ps) = 
    if null cs then ts else 
       let (toks, pls) = splitMixToken ts in
	   toks ++ getCompoundTokenList cs ps ++ pls

-- | reconstruct tokens of compound list  
getCompoundTokenList :: [Id] -> [Pos] -> [Token]
getCompoundTokenList cs ps = concat $ expandPos (:[]) ("[", "]") 
	      -- although positions will be replaced (by scan)
			     (map getPlainTokenList cs) ps

-- | reconstruct the token list of an 'Id'.
-- Replace top-level places with the input String 
getTokenList :: String -> Id -> [Token]
getTokenList placeStr (Id ts cs ps) = 
    let convert =  map (\ t -> if isPlace t then t {tokStr = placeStr} else t) 
    in if null cs then convert ts else 
       let (toks, pls) = splitMixToken ts in
	   convert toks ++ getCompoundTokenList cs ps ++ convert pls

-- | update token positions.
-- return remaining positions 
setToksPos :: [Token] -> [Pos] -> ([Token], [Pos])
setToksPos (h:ts) (p:ps) = 
    let (rt, rp) = setToksPos ts ps
	in (h {tokPos = p} : rt, rp)
setToksPos ts ps = (ts, ps)

-- | update positions in 'Id'.
-- return remaining positions 
setPlainIdePos :: Id -> [Pos] -> (Id, [Pos]) 
setPlainIdePos (Id ts cs _) ps =
    if null cs then 
       let (newTs, restPs) = setToksPos ts ps
	   in (Id newTs cs [], restPs)
    else let (toks, pls) = splitMixToken ts
	     ttail l = if null l then l else tail l
	     (front, ps2) = setToksPos toks ps
	     (newCs, ps3, ps4) = foldl ( \ (prevCs, seps, rest) a -> 
				  let (c1, qs) = setPlainIdePos a rest
				  in (c1: prevCs, head qs : seps, ttail qs))
			   ([], [head ps2], ttail ps2) cs
	     (newPls, ps7) = setToksPos pls ps4
           in (Id (front ++ newPls) (reverse newCs) (reverse ps3), ps7)

-- | update positions in 'Id' also using positions from arguments.
-- There must be sufficiently many positions
setIdePos :: (PosItem a) => Id -> [a] -> [Pos] -> Id
setIdePos i ar pl =
    fst $ setPlainIdePos i $ mergePos pl $ map getMyPos ar
    where mergePos (p:ps) (q:qs) =
	      if p <= q then p : mergePos ps (q:qs) 
		 else q : mergePos (p:ps) qs 
	  mergePos [] qs = qs
	  mergePos ps [] = ps

-- | compute a meaningful single position from an 'Id' for diagnostics 
posOfId :: Id -> Pos
posOfId (Id ts _ _) = let l = dropWhile isPlace ts 
		      in if null l then -- for invisible "__ __" (only places)
			   headPos $ map tokPos ts
			 else tokPos $ head l

-- | simple ids are just tokens 
type SIMPLE_ID = Token

-- | a 'Token' with 'nullPos'
mkSimpleId :: String -> Token
mkSimpleId s = Token s nullPos

-- | a 'SIMPLE_ID' as 'Id'
simpleIdToId :: SIMPLE_ID -> Id
simpleIdToId sid = Id [sid] [] []

-- | efficiently test for a singleton list 
isSingle :: [a] -> Bool
isSingle [_] = True
isSingle _   = False

-- | test for a 'SIMPLE_ID'
isSimpleId :: Id -> Bool
isSimpleId (Id ts cs _) = null cs && isSingle ts

---- some useful predicates for Ids -------------------------------------

-- | number of 'place' in 'Id'

placeCount :: Id -> Int
placeCount (Id tops _ _) = length $ filter isPlace tops

-- | has no (toplevel) 'place'
isOrdAppl :: Id -> Bool
isOrdAppl = not . isMixfix

-- | has a 'place'
isMixfix :: Id -> Bool
isMixfix (Id tops _ _) = any isPlace tops 

-- | ends with a 'place'
isPrefix :: Id -> Bool
isPrefix (Id tops _ _) = not (null tops) && not (isPlace (head tops)) 
			 && isPlace (last tops)

-- | starts with a 'place'
isPostfix :: Id -> Bool
isPostfix (Id tops _ _) = not (null tops) &&  isPlace (head  tops) 
			  && not (isPlace (last tops)) 

-- | is classical infix id with three tokens, the middle one is a non-place 
isInfix2 :: Id -> Bool
isInfix2 (Id ts _ _) = 
    case ts of 
	    [e1, e2, e3] -> isPlace e1 && not (isPlace e2) 
			    && isPlace e3 
	    _ -> False

-- | starts and ends with a 'place'
isInfix :: Id -> Bool
isInfix (Id tops _ _) = not (null tops) &&  isPlace (head tops) 
			&& isPlace (last tops)

-- | has a 'place' but neither starts nor ends with one
isSurround :: Id -> Bool
isSurround i@(Id tops _ _) = not (null tops) && (isMixfix i)
			     && not (isPlace (head tops)) 
				    && not (isPlace (last tops)) 

-- | has a compound list
isCompound :: Id -> Bool
isCompound (Id _ cs _) = not $ null cs

---- helper class -------------------------------------------------------

{- | This class is derivable with DrIFT.
   Its main purpose is to have a function that operates on
   constructors with a 'Pos' or list of 'Pos' field. During parsing, mixfix
   analysis and ATermConversion this function might be very useful.
-}

class PosItem a where
    up_pos    :: (Pos -> Pos)    -> a -> a
    up_pos_l  :: ([Pos] -> [Pos]) -> a -> a
    get_pos   :: a -> Maybe Pos  -- not a nullPos  
    get_pos_l :: a -> Maybe [Pos]
    up_pos_err  :: String -> a
    up_pos_err fn = 
	error ("function \"" ++ fn ++ "\" is not implemented")
    up_pos _    = id
    up_pos_l _  = id
    get_pos   _ = Nothing
    get_pos_l _ = Nothing

-- a Pos list should not contain nullPos
    
-------------------------------------------------------------------------

-- | get a reasonable position
getMyPos :: PosItem a => a -> Pos
getMyPos a = 
    case get_pos a of
    Just p -> p
    Nothing -> 
	case get_pos_l a of 
	Just l -> headPos l
	Nothing -> nullPos

-- | get a reasonable position for a list
posOf :: PosItem a => [a] -> Pos
posOf l = if null l then nullPos else 
	  let q = getMyPos $ head l 
	      in if q == nullPos then posOf $ tail l
		 else q

-- | get a reasonable position for a list with an additional position list
firstPos :: PosItem a => [a] -> [Pos] -> Pos
firstPos l ps = let p = posOf l in 
			if p == nullPos then headPos ps else p

-- | handcoded instance
instance PosItem Token where
    up_pos fn1 (Token aa ab) = (Token aa (fn1 ab))
    get_pos (Token _ ab) = Just ab

-- | handcoded instance
instance PosItem Id where
    up_pos_l fn1 (Id aa ab ac) = (Id aa ab (fn1 ac))
    get_pos_l (Id _ _ ac) = Just ac
    get_pos = Just . posOfId
