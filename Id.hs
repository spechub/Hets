
{- HetCATS/Id.hs
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

module Id where

import Char

-- identifiers, fixed for all logics

type Pos = (Int, Int) -- line, column

nullPos :: Pos 
nullPos = (0,0)
 
type Region = (Pos,Pos)
 
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

-- special tokens
type Keyword = Token
type TokenOrPlace = Token
 
place :: String
place = "__"

isPlace :: TokenOrPlace -> Bool
isPlace (Token t _) = t == place
 
-- an identifier may be mixfix (though not for a sort) and compound
-- TokenOrPlace list must be non-empty!
data Id = Id [TokenOrPlace] [Id] [Pos] 
                                 -- pos of "[", commas, "]" 
	  deriving (Show)
-- for pretty printing see PrettyPrint.hs

instance Eq Id where
    Id tops1 ids1 _ == Id tops2 ids2 _ = tops1 == tops2 && ids1 == ids2

instance Ord Id where
    Id tops1 ids1 _ <= Id tops2 ids2 _ = 
	if tops1 == tops2 then ids1 <= ids2 else tops1 <= tops2

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

-- compute a meaningful single position for diagnostics

posOfId :: Id -> Pos
posOfId (Id [] _ _) = error "Id.posOfId"
posOfId (Id ts _ _) = let l = dropWhile isPlace ts 
		      in if null l then -- for invisible "__ __" (only places)
			   let h = head ts 
			       (lin, col) = tokPos h
			       in (lin, col + length (tokStr h))
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
isPrefix (Id tops _ _) = (not . isPlace . head) tops 
			 && (isPlace . last) tops 

isPostfix :: Id -> Bool
isPostfix (Id tops _ _) = (isPlace . head) tops 
			  && (not . isPlace . last) tops 

isInfix2 :: Id -> Bool
isInfix2 (Id tops _ _)
    | length tops == 3 = (isPlace . head) tops 
			 && (isPlace . last) tops
			 && (not . isPlace . head . tail) tops
    | otherwise = False

isInfix :: Id -> Bool
isInfix (Id tops _ _) = (isPlace . head) tops 
			&& (isPlace . last) tops

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
    up_pos _ _   = up_pos_err "up_pos"
    up_pos_l _ _ = up_pos_err "up_pos_l"
    get_pos   _ = error "function \"get_pos\" not implemented" 
    get_pos_l _ = error "function \"get_pos_l\" not implemented"    
    
-------------------------------------------------------------------------

-- Two fine instances, DrIFTed but handcopied
instance PosItem Token where
    up_pos fn1 (Token aa ab) = (Token aa (fn1 ab))
    get_pos (Token _ ab) = Just ab

instance PosItem Id where
    up_pos_l fn1 (Id aa ab ac) = (Id aa ab (fn1 ac))
    get_pos_l (Id _ _ ac) = Just ac
