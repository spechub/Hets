module Id where

import Char
-- identifiers, fixed for all logics

type Pos = (Int, Int) -- line, column
 
type Region = (Pos,Pos)
 
-- tokens as supplied by the scanner
data Token = Token String Pos -- deriving (Show, Eq, Ord)
showTok (Token t _) = t

instance Eq Token where
   Token s1 _ == Token s2 _ = s1 == s2
 
instance Ord Token where
   Token s1 _  <= Token s2 _ = s1 <= s2

showSepList :: ShowS -> (a -> ShowS) -> [a] -> ShowS
showSepList _ _ [] = showString ""
showSepList _ f [x] = f x
showSepList s f (x:r) = f x . s . showSepList s f r
 
instance Show Token where
   showsPrec _ = showString . showTok
   showList = showSepList (showString "") shows

-- spezial tokens
type Keyword = Token
type TokenOrPlace = Token
 
place = "__"

isPlace(Token t _) = t == place
 
-- an identifier may be mixfix (though not for a sort) and compound
-- TokenOrPlace list must be non-empty!
data Id = Id [TokenOrPlace] [Id] deriving (Eq, Ord)
 
splitMixToken l = let (pls, toks) = span isPlace (reverse l) in
	      (reverse toks, reverse pls)

showId (Id ts is) = 
	let (toks, places) = splitMixToken ts 
            comps = if null is then showString "" else shows is 
	in
        showList toks . comps . showList places

instance Show Id where
    showsPrec _ = showId 
