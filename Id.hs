module Id where

import Char
import Pretty
import PrettyPrint
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

showSepList :: ShowS -> (a -> ShowS) -> [a] -> ShowS
showSepList _ _ [] = showString ""
showSepList _ f [x] = f x
showSepList s f (x:r) = f x . s . showSepList s f r

instance PrettyPrint Token where
 printText0 t = text (tokStr t)

-- special tokens
type Keyword = Token
type TokenOrPlace = Token
 
place = "__"

isPlace(Token t _) = t == place
 
-- an identifier may be mixfix (though not for a sort) and compound
-- TokenOrPlace list must be non-empty!
data Id = Id [TokenOrPlace] [Id] [Pos] deriving (Eq, Ord, Show)
                                 -- pos of "[", commas, "]" 

showId (Id ts is _) = 
	let (toks, places) = splitMixToken ts 
            comps = if null is then showString "" else 
                  showString "[" . showSepList (showString ",") showId is
		  . showString "]"
	    showToks = showSepList (showString "") showTok
	in  showToks toks . comps . showToks places

splitMixToken l = let (pls, toks) = span isPlace (reverse l) in
	      (reverse toks, reverse pls)

instance PrettyPrint Id where
 printText0 i = text (showId i "")

-- Simple Ids

type SIMPLE_ID = Token

