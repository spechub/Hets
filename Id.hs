module Id where

import Char
-- identifiers, fixed for all logics

type Pos = (Int, Int) -- line, column

nullPos :: Pos 
nullPos = (0,0)
 
type Region = (Pos,Pos)
 
-- tokens as supplied by the scanner
data Token = Token { showTok :: String
		   , tokPos :: Pos
		   } -- not deriving (Show, Eq, Ord)!

instance Eq Token where
   Token s1 _ == Token s2 _ = s1 == s2
 
instance Ord Token where
   Token s1 _  <= Token s2 _ = s1 <= s2

instance Show Token where
   showsPrec _ = showString . showTok
   showList = showPlainList


showPlainList :: Show a => [a] -> ShowS
showPlainList = showSepList (showString "") shows

showSepList :: ShowS -> (a -> ShowS) -> [a] -> ShowS
showSepList _ _ [] = showString ""
showSepList _ f [x] = f x
showSepList s f (x:r) = f x . s . showSepList s f r

-- spezial tokens
type Keyword = Token
type TokenOrPlace = Token
 
place = "__"

isPlace(Token t _) = t == place
 
-- an identifier may be mixfix (though not for a sort) and compound
-- TokenOrPlace list must be non-empty!
data Id = Id [TokenOrPlace] [Id] deriving (Eq, Ord)
 
instance Show Id where
    showsPrec _ = showId 

showId (Id ts is) = 
	let (toks, places) = splitMixToken ts 
            comps = if null is then showString "" else shows is 
	in
        shows toks . comps . shows places

splitMixToken l = let (pls, toks) = span isPlace (reverse l) in
	      (reverse toks, reverse pls)

-- Simple Ids

type SIMPLE_ID = Token

