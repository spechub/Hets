
module Common.ATerm.ReadWrite (

	readATerm,       -- :: String -> ATermTable
	writeATerm,      -- :: ATermTable -> String
	writeSharedATerm,-- :: ATermTable -> String
) where

{-
	Author: Joost Visser, CWI, 2002
        Changed by: Klaus Luettich & Felix Reckers, 2002-2003

	This module contains functions for reading and writing ATerms
        from and to Strings. Two ATerm formats are supported:

		AT:	plain (non-shared) textual ATerms
		TAF:	shared textual ATerms

	The binary ATerm format (BAF) is not supported.

	Current limitations:

		BLOBS and place-holders are not supported.

		

-}

import Common.ATerm.AbstractSyntax

-- added by KL
import Char
import List
import Array
import Data.FiniteMap
import Common.Lib.Pretty
-- import Numeric don't use showInt: can't show negative numbers

--- From String to ATerm ------------------------------------------------------


readATerm :: String -> ATermTable 
readATerm ('!':str)	= 
    let ((at,_),_,_,_) = readTAF emptyATermTable str emptyRTable 0 in at
readATerm str		= 
    let ((at,_),_)     = readAT  emptyATermTable (dropSpaces str)      in at


-- non-shared --

readAT :: ATermTable -> String -> ((ATermTable,Int),String)
readAT at ('[':str)	   =  let ((at',kids), str') = readATs at ']' (dropSpaces str)
                                  ((at'',ann), str'')= readAnn at' (dropSpaces str')
			      in (addATerm (ShAList kids ann) at'', str'')
readAT at str@(c:cs)
  | isIntHead c		   =  let (i,str') = span isDigit cs
                                  ((at',ann), str'') = readAnn at (dropSpaces str')
                              in (addATerm (ShAInt (read (c:i)) ann) at',str'')
  | c=='(' || isAFunChar c || c=='"' =  
	     let (c',str') = readAFun str
		 ((at',kids), str'')  = readParenATs at (dropSpaces str')
                 ((at'',ann), str''') = readAnn at' (dropSpaces str'')
 	     in (addATerm (ShAAppl c' kids ann) at'', str''')
  | otherwise              = error $ error_aterm (take 5 str) 


readAFun :: String -> (String,String)
readAFun ('"':str)	=  let (c,('"':str')) = spanNotQuote' str 
                           in (quote c,str')
readAFun str		=  spanAFunChar str

readParenATs :: ATermTable -> String -> ((ATermTable,[Int]),String)
readParenATs at ('(':str) =  readATs at ')' (dropSpaces str)
readParenATs at str	  =  ((at,[]),str)

readATs :: ATermTable -> Char -> String -> ((ATermTable,[Int]),String)
readATs at par s@(p:str)  | par == p   = ((at,[]),str)
			  | otherwise  = readATs1 at par s

readATs1 :: ATermTable -> Char -> String -> ((ATermTable,[Int]),String) 
readATs1 at par str	=  let ((at',t),str')    = readAT   at  (dropSpaces str)
			       ((at'',ts),str'') = readATs' at' par (dropSpaces str')
			   in ((at'',t:ts),str'')

readATs' :: ATermTable -> Char -> String -> ((ATermTable,[Int]),String) 
readATs' at par (',':str)  = readATs1 at par (dropSpaces str)
readATs' at par s@(p:str)  | par == p  = ((at,[]),str)
                           | otherwise = error (error_paren (take 5 s))

readAnn :: ATermTable -> String -> ((ATermTable,[Int]),String)
readAnn at ('{':str) = readATs at '}' (dropSpaces str)
readAnn at str       = ((at,[]),str) 


-- shared --

readTAF :: ATermTable -> String 
	-> ReadTable -> Int -> ((ATermTable,Int),String,ReadTable,Int)
readTAF at ('#':str) tbl l =  
    let (i,str') = spanAbbrevChar str
    in (addATerm (getAbbrevTerm (deAbbrev i) at tbl) at, 
	str',tbl,
	l+(length i)+1)    
readTAF at ('[':str) tbl l =  
    let ((at',kids), str',tbl',l') = readTAFs at ']' (dropSpaces str) tbl 1
        ((at'',ann),str'',tbl'',l'') = readAnnTAF at' (dropSpaces str') tbl' 0 
	t            = ShAList kids ann      
	tbl'''       = condAddElement (addRAbbrev at_fin) (l''+l') tbl''
	at_t@(at_fin,_) = addATerm t at''
	in (at_t, str'',tbl''',l+l'+l'')
readTAF at str@(x:xs) tbl l 
  | isIntHead x =  
      let (i,str')   = span isDigit xs
          l'         = length (x:i)
          ((at',ann),str'',tbl',l'') = readAnnTAF at str' tbl 0
	  t          = ShAInt (read (x:i)) ann 
	  tbl''      = condAddElement (addRAbbrev at_fin) (l'+l'') tbl'
	  at_t@(at_fin,_) = addATerm t at'
      in (at_t,str'',tbl'', l+l'+l'')
  |isAFunChar x || x=='"' || x=='(' = 
      let (c,str')           = readAFun str
	  ((at',kids), str'',tbl',l') = 
		readParenTAFs at (dropSpaces str') tbl 0
          ((at'',ann),str''',tbl'',l'') = 
		readAnnTAF at' (dropSpaces str'') tbl' 0
	  t                  = ShAAppl c kids ann
	  l'''   = (length c) + l'+l''
	  tbl''' = condAddElement (addRAbbrev at_fin) l''' tbl''
	  at_t@(at_fin,_) = addATerm t at''
 	  in (at_t, str''',tbl''',l''')
  | otherwise             = error $ error_saterm (take 5 str)

readParenTAFs :: ATermTable -> String -> ReadTable 
	      -> Int -> ((ATermTable,[Int]),String,ReadTable,Int)
readParenTAFs at ('(':str) tbl l  =  readTAFs at ')'(dropSpaces str) tbl (l+1)
readParenTAFs at str       tbl l  =  ((at,[]),str,tbl,l)

readTAFs :: ATermTable -> Char -> String -> ReadTable 
	 -> Int -> ((ATermTable,[Int]),String,ReadTable,Int)
readTAFs at par s@(p:str) tbl l | par == p  = ((at,[]),str,tbl,l+1)
                                | otherwise = readTAFs1 at par s tbl l

readTAFs1 :: ATermTable -> Char -> String -> ReadTable -> Int 
	  -> ((ATermTable,[Int]),String,ReadTable,Int)
readTAFs1 at par str tbl l = 
    let ((at',t),str',tbl',l')= readTAF at (dropSpaces str) tbl l
	((at'',ts),str'',tbl'',l'') = 
	    readTAFs' at' par (dropSpaces str') tbl' l'
    in ((at'',t:ts),str'',tbl'',l'')

readTAFs' :: ATermTable -> Char -> String -> ReadTable -> Int 
			-> ((ATermTable,[Int]),String,ReadTable,Int)
readTAFs' at par (',':str) tbl l = readTAFs1 at par (dropSpaces str) tbl (l+1)
readTAFs' at par s@(p:str) tbl l | par == p  = ((at,[]),str,tbl,l+1)
                                 | otherwise = error $ error_paren (take 5 s)

readAnnTAF :: ATermTable -> String -> ReadTable -> Int 
	   -> ((ATermTable,[Int]),String,ReadTable,Int)
readAnnTAF at ('{':str) tbl l = readTAFs at '}' (dropSpaces str) tbl (l+1) 
readAnnTAF at str       tbl l = ((at,[]),str,tbl,l)


-- helpers --

dropSpaces :: String -> String 
dropSpaces		= dropWhile isSpace

spanAFunChar :: String -> (String,String)
spanAFunChar		= span isAFunChar

isAFunChar :: Char -> Bool
isAFunChar c		= (isAlphaNum c) || (c `elem` "-_*+")


{-spanNotQuote :: String -> (String,String)
spanNotQuote 		= span (/='"')
-}
spanAbbrevChar :: String -> (String,String)
spanAbbrevChar		= span (`elem` toBase64)

isIntHead :: Char -> Bool
isIntHead c		= (isDigit c) || (c=='-')

quote :: String -> String
quote str		= ('"':str)++"\""

spanNotQuote' :: String -> (String,String)
spanNotQuote' []		= ([],[])
spanNotQuote' xs@('"':_xs')  	= ([],xs)
spanNotQuote' ('\\':'"':xs')	= ('\\':'"':ys,zs) 
                                  where (ys,zs) = spanNotQuote' xs'
spanNotQuote' (x:xs')	= (x:ys,zs) 
                                  where (ys,zs) = spanNotQuote' xs'
{-
span :: (a -> Bool) -> [a] -> ([a],[a])
span p []            = ([],[])
span p xs@(x:xs')
	 | p x       = (x:ys, zs)
	 | otherwise = ([],xs)
                       where (ys,zs) = span p xs'
-}

condAddElement ::(Next_Abb tab) => (tab -> tab) -> Int -> tab -> tab
condAddElement add l tbl = 
    -- length $ abbrev (maxBound::Int) == 7, so every ATerm with a
    -- string size greater than 7 need to be added
    if l>7 || (next_abbrev_len tbl) < l then
       add tbl
    else
       tbl

class Next_Abb a where
    next_abbrev_len :: a -> Int

--- From ATerm to String  -----------------------------------------------------

-- a helper data Type for ShowS functions paired with the associated length
data Doc_len = Doc_len {-# UNPACK #-} !Doc {-# UNPACK #-} !Int

data Write_struct = WS {-# UNPACK #-} !WriteTable {-# UNPACK #-} !Doc_len

-- an error generated every time when at least one non-empty
-- ATermString is expected!! The Argument should be the thoring
-- function name.
fatal_error :: String -> a 
fatal_error fn = error (fn++": empty SharedATermString found!!")

{- showFun :: ShowS_len -> ShowS
showFun = fst
showLen :: ShowS_len -> Int
showLen = snd-}

--type ShowS = String -> String

writeATerm :: ATermTable -> String
writeATerm at           = writeAT at $ ""

writeSharedATerm :: ATermTable -> String 
writeSharedATerm at	= 
    case writeTAF at emptyWTable of
    (WS _ (Doc_len doc _)) -> (rend (char '!'<>doc)) 
    _ -> fatal_error "writeSharedATerm"
    where rend d = fullRender OneLineMode 100 1.5 string_txt_comp "" d
	  string_txt_comp td = case td of
			       Chr  c -> showChar   c
			       Str  s -> showString s
			       PStr s -> showString s

-- non-shared --
{-
writeAT        :: ATermTable -> ShowS
writeAT at     =  
    case (getATerm at) of
	     (ShAAppl c ts as) -> evalShowS_len (writeATermAux c) (writeAT' at ts) . evalShowS_len writeParenthesiseAnn (writeAT' at as) 
	     (ShAList ts as)   -> convertToShowS (bracket (convertFromShowS (evalShowS_len commaSep (writeAT' at ts)))) . evalShowS_len (writeParenthesiseAnn) (writeAT' at as)	
             (ShAInt i as)     -> showString (show i) . evalShowS_len writeParenthesiseAnn (writeAT' at as) 
-}
writeAT :: ATermTable -> ShowS
writeAT at     =  
    case (getATerm at) of
	     (ShAAppl c ts as) -> writeATermAux c (writeAT' at ts) . writeParenthesiseAnn (writeAT' at as) 
	     (ShAList ts as)   -> bracket (commaSep (writeAT' at ts)) . writeParenthesiseAnn (writeAT' at as)	
             (ShAInt i as)     -> showString (show i) . writeParenthesiseAnn (writeAT' at as)
-- don't use showInt: can't show negative numbers
writeAT' :: ATermTable -> [Int] -> [ShowS]
writeAT' _at []     = []
writeAT' at (i:is) = let at' = getATermByIndex1 i at 
			 str = writeAT at'
			 strs = writeAT' at is
		     in (str:strs)    
		 	    	 		    
		      
--shared--
writeTAF :: ATermTable -> WriteTable -> Write_struct
writeTAF at tbl =  
    case indexOf at tbl of
    (Just s) -> WS tbl s 
    Nothing  -> WS (condAddElement (addWAbbrev at) len tbl') d_len
    where (WS tbl' d_len@(Doc_len _ len)) = writeTAF' at tbl
	  -- risking a faulty writeTAF' implementation

writeTAF' :: ATermTable -> WriteTable -> Write_struct
writeTAF' at tbl = 
    case getATerm at of
    (ShAAppl c ts as) -> 
	     let (WS tbl' kids)     = writeTAFs at ts tbl
                 (WS tbl'' kidsAnn) = writeTAFs at as tbl'
             in WS tbl'' $ dlConcat (writeATermAuxS c kids) 
		                       (parenthesiseAnnS kidsAnn)
    (ShAList ts as)   -> 
	     let (WS tbl' kids)     = writeTAFs at ts tbl
		 (WS tbl'' kidsAnn) = writeTAFs at as tbl'
             in WS tbl'' $ 
		     dlConcat (bracketS kids) 
		                 (parenthesiseAnnS kidsAnn)
    (ShAInt i as)     -> 
	     let (WS tbl' kidsAnn) = writeTAFs at as tbl
		 istr = show i
		 -- don't use showInt: can't show negative numbers
	     in WS tbl' $ 
		      dlConcat (Doc_len (integer i) (length istr)) 
		                  (parenthesiseAnnS kidsAnn)

dlConcat :: Doc_len -> Doc_len -> Doc_len		
{-showSConcat ShowS_len_empty ShowS_len_empty = fatal_error "showSConcat"
showSConcat ShowS_len_empty showS_len = showS_len
showSConcat showS_len ShowS_len_empty = showS_len-}
dlConcat s1@(Doc_len sf1 sl1) s2@(Doc_len sf2 sl2) 
    | sl1 == 0 && sl2 == 0 = fatal_error "showSConcat"
    | sl1 == 0  = s2 
    | sl2 == 0  = s1
    | otherwise = Doc_len (sf1 <> sf2) (sl1 + sl2)

{-# INLINE dlConcat #-}
{-# INLINE dlConcat_comma #-}
dlConcat_comma :: Doc_len -> Doc_len -> Doc_len		
{-showSConcat_comma ShowS_len_empty ShowS_len_empty = 
    fatal_error "showSConcat_comma"
showSConcat_comma ShowS_len_empty (ShowS_len sf sl) = 
    ShowS_len (sf . showChar ',') (sl + 1)
showSConcat_comma (ShowS_len sf sl) ShowS_len_empty = 
    ShowS_len (sf . showChar ',') (sl + 1)-}
dlConcat_comma (Doc_len sf1 sl1) (Doc_len sf2 sl2) 
    | sl1 == 0 && sl2 == 0 = fatal_error "showSConcat"
    | sl1 == 0  = Doc_len (sf2 <>comma) (sl2 + 1)
    | sl2 == 0  = Doc_len (sf1 <>comma) (sl1 + 1)
    | otherwise = Doc_len (sf1 <> sf2 <> comma) (sl1 + sl2 + 1)


-- produce a String function with a comma seperated string converted ATerms
writeTAFs :: ATermTable -> [Int] -> WriteTable -> Write_struct
writeTAFs _  [] tbl = (WS tbl $ Doc_len empty 0)
writeTAFs at inds tbl = writeTAFs' inds (WS tbl $ Doc_len empty 0)
    where writeTAFs' :: [Int] -> Write_struct -> Write_struct
	  writeTAFs' [] _ = error "not reachable"
	  writeTAFs' [i] (WS t s) = 
	      let (WS t' s') = wT t i
	      in WS t' (dlConcat s s')
	  writeTAFs' (i:is) (WS t s) = 
	      let (WS t' s')   = wT t i
	      in writeTAFs' is (WS t' (dlConcat_comma s s'))
	  wT :: WriteTable -> Int -> Write_struct
	  wT t i = writeTAF (getATermByIndex1 i at) t

{-    let (WS tbl' showS_len_i) = foldr wTAF (WS tbl ShowS_len_empty) (init inds)
	(WS tbl'' showS_len_l) = wT (last inds) tbl'
	wT :: Int -> WriteTable -> Write_struct
	wT i t = writeTAF (getATermByIndex1 i at) t
	wTAF :: Int -> Write_struct -> Write_struct
	wTAF i (WS tbl' showS_len2) = 
	    let (WS tbl'' (ShowS_len sf1 sl1)) = 
		    wT i tbl' 
		sf1' = sf1 . showChar ','
	      in WS tbl'' $ 
		    showSConcat (ShowS_len sf1' (sl1+1)) 
				showS_len2
    in WS tbl'' $ showSConcat showS_len_i showS_len_l
-}
{-writeTAFs at [] tbl	=  ([],tbl)
writeTAFs at (i:is) tbl = let (at',t) = getATermByIndex i at
                              (str,tbl') = writeTAF at' tbl
			      (strs,tbl'') = writeTAFs at is tbl'
			  in (str:strs , tbl'')
-}

-- helpers --
{-
convertToShowS :: ShowS_len -> ShowS
convertToShowS (ShowS_len {showFun=fun, showLen=len}) = fun

convertFromShowS :: ShowS -> ShowS_len
convertFromShowS s = ShowS_len{ showFun=s , showLen=0 }

evalShowS_len :: ([ShowS_len] -> ShowS_len) -> [ShowS] -> ShowS
evalShowS_len f s = convertToShowS $ f $ map convertFromShowS s 
-}

writeATermAux :: String -> [ShowS] -> ShowS
writeATermAux c [] = showString c
writeATermAux c ts = showString c . parenthesise (commaSep ts)

writeATermAuxS :: String -> Doc_len -> Doc_len
{-writeATermAuxS c ShowS_len_empty = 
    ShowS_len (showString c) (length c)-}
writeATermAuxS c doc_len@(Doc_len _ l)	 
    | l == 0 = Doc_len (text c) (length c)
    | l >  0 = Doc_len (text c <> pf) (length c + pl)
    | otherwise = error "writeATermAuxS: negative length"
    where (Doc_len pf pl) = parenthesiseS doc_len

writeParenthesiseAnn :: [ShowS] -> ShowS
writeParenthesiseAnn [] = id
writeParenthesiseAnn as = parenthesiseAnn $ commaSep as

{-writeParenthesiseAnnS :: [ShowS_len] ->  ShowS_len
writeParenthesiseAnnS [] = ShowS_len_empty
writeParenthesiseAnnS as = parenthesiseAnnS (commaSepS as)
-}
commaSep :: [ShowS] -> ShowS
commaSep [] = id
commaSep str = foldr1 (\x y-> x . showChar ',' . y) str

{-commaSepS :: [ShowS_len] -> ShowS_len
commaSepS []   = ShowS_len_empty
commaSepS strs = foldr1 sepConc strs
    where sepConc :: ShowS_len -> ShowS_len -> ShowS_len
	  sepConc (ShowS_len sf1 sl1) (ShowS_len sf2 sl2) =
	      ShowS_len (sf1 . showChar ',' . sf2)
			(sl1 + 1 + sl2)
	  sepConc _ _ = fatal_error "sepConc in commaSepS"-}
{-let (sfs,lens) = unzip strs
		 in (commaSep sfs,max (sum lens + length lens - 1) 0)
-}
bracket, parenthesise, parenthesiseAnn :: ShowS -> ShowS 
bracket         str = showChar '[' . str . showChar ']'
parenthesise    str = showChar '(' . str . showChar ')'
parenthesiseAnn str = showChar '{' . str . showChar '}'

bracketS, parenthesiseS, parenthesiseAnnS :: Doc_len -> Doc_len
--bracketS         ShowS_len_empty   = 
--    ShowS_len (showChar '[' . showChar ']') 2
bracketS         (Doc_len d dl) 
    | dl == 0   = Doc_len (brackets empty) 2
    | otherwise = Doc_len (brackets d) (dl+2)
-- parenthesiseS    ShowS_len_empty   = ShowS_len_empty
parenthesiseS    s@(Doc_len d dl) 
    | dl == 0   = s
    | otherwise = Doc_len (parens d) (dl+2)
--parenthesiseAnnS ShowS_len_empty   = ShowS_len_empty
parenthesiseAnnS s@(Doc_len d dl) 
    | dl == 0   = s
    | otherwise = Doc_len (braces d) (dl+2)

--- Tables of ATerms ----------------------------------------------------------

-- These Tables consist of FiniteMaps, because all ATerms are indexed
-- with an Int in the second component of the ATermTable. So
-- ATermIndex is the Index that is given by getATermIndex.

-- Map: Abbrev     -> ATermIndex
data ReadTable  = RTab (FiniteMap Int Int) !Int

instance Next_Abb ReadTable where
    next_abbrev_len = next_abbrev_R_len 

-- 1st Map: ATermIndex -> Abbrev
-- TODO: implement 2nd Map as WriteCache 
--         (sf::ShowS,length of String in sf::Int) .. done
data WriteTable = WTab (FiniteMap Int Doc_len) 
                       {-# UNPACK #-} !(Doc_len,Int)

instance Next_Abb WriteTable where
    next_abbrev_len = next_abbrev_W_len

emptyRTable :: ReadTable
emptyRTable = RTab emptyFM 0

emptyWTable :: WriteTable
emptyWTable = WTab emptyFM (abbrevD 0,0)

-- abbrev of top-level / selected ATerm for wirting
indexOf :: ATermTable -> WriteTable -> Maybe (Doc_len)
indexOf at (WTab ai_abb_map _) = 
    let ai = getTopIndex at
    in if ai == -1 
       then Nothing
       else lookupFM ai_abb_map ai
{-
lengthOfShATermInd :: Int -> WriteTable -> Maybe Int
lengthOfShATermInd ai (WTab _ lmap _) = IntMap.lookup ai lmap
-}

-- top-level / selected ATerm gets next abbrev and a length
addWAbbrev :: ATermTable -> WriteTable -> WriteTable
addWAbbrev at (WTab ai_abb_map (da,i)) =  
    let ai = getTopIndex at
    in if ai == -1 
       then error (show (getATerm at) ++ " not found")
       else WTab (addToFM ai_abb_map ai da) 
		 (abbrevD (i+1),i+1)

-- the String Argument is not used and serves as dummy for ease of code change
addRAbbrev :: ATermTable -> ReadTable -> ReadTable
addRAbbrev at (RTab abb_ai_map i) =  
    let ai = getTopIndex at
    in if ai == -1 
       then error (show (getATerm at) ++ " not found")
       else RTab (addToFM abb_ai_map i ai) (i+1)

getAbbrevTerm :: Int -> ATermTable -> ReadTable -> ShATerm
getAbbrevTerm i at (RTab abb_ai_map _) =  
    let i'    = lookupWithDefaultFM abb_ai_map (err) i
	err   = error ("Index "++show i++"not found")
    in snd $  getATermByIndex i' at 

{-
(!!!)              :: [b] -> Integer -> b
(x:_)  !!! 0       =  x
(_:xs) !!! n | n>0 =  xs !!! (n-1)
(_:_)  !!! _       =  error "!!!: negative index"
[]     !!! _       =  error "!!!: index too large"
-}
--- Base 64 encoding ----------------------------------------------------------

mkAbbrev :: Int -> [Char]
mkAbbrev x
  | x == 0	= [revBase64Array ! 0]
  | otherwise   = reverse (mkAbbrevAux x)

mkAbbrevAux :: Int -> [Char]
mkAbbrevAux x
  | x == 0	= []
  | x > 0	= (revBase64Array ! m:mkAbbrevAux d) 
  | otherwise   = error ("mkAbbrevAux: Int "++ show x++" to big")
  where (d,m) = divMod x 64

deAbbrev :: [Char] -> Int
deAbbrev x		=  deAbbrevAux (reverse x)

deAbbrevAux :: [Char] -> Int
deAbbrevAux []		=  0
deAbbrevAux (c:cs)	=  let i = base64Array ! c
               	               r = deAbbrevAux cs			       
			   in seq r (i + 64*r)

revBase64Array :: Array Int Char
revBase64Array = array (0,63) $ zip integerList toBase64
    where integerList :: [Int]
	  integerList = [0..63]

base64Array :: Array Char Int
base64Array = array ('+','z') $ zip toBase64 integerList
    where integerList :: [Int]
	  integerList = [0..63]

toBase64 :: [Char]
toBase64 =
  [ 'A','B','C','D','E','F','G','H','I','J','K','L','M','N','O','P',
    'Q','R','S','T','U','V','W','X','Y','Z','a','b','c','d','e','f',
    'g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v',
    'w','x','y','z','0','1','2','3','4','5','6','7','8','9','+','/' 
  ]

-- helpers --
abbrevD :: Int -> Doc_len
abbrevD i = let abbStr = abbrev i 
            in (Doc_len (text abbStr) (length abbStr))

abbrev :: Int -> [Char]
abbrev i = '#' : (mkAbbrev i)

next_abbrev_W_len :: WriteTable -> Int
next_abbrev_W_len (WTab _ (_,len)) = len

next_abbrev_R_len :: ReadTable -> Int
next_abbrev_R_len (RTab _ siz) = length $ abbrev (siz+1)

-- error messages --------------------

error_paren (s:str) = "Can't parse '" ++ [s] ++ "',expecting \",\" or matching parenthesis \nFollowing characters are:" ++ str  
error_aterm (s:str) = "Can't parse '" ++ [s] ++ "', expecting ATermAppl, ATermList or ATermInt\nFollowing characters are:" ++ str
error_saterm (s:str) = "Can't parse '" ++ [s] ++ "', expecting Abbreviate, ATermAppl, ATermList or ATermInt\nFollowing characters are:" ++ str