
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

import Common.Lib.Map hiding (map,(!))
import List
import Array


--- From String to ATerm ------------------------------------------------------


readATerm :: String -> ATermTable 
readATerm ('!':str)	= 
    let ((at,_),_,_,_) = readTAF emptyATermTable str emptyTable 0 in at
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
  | c=='(' || isAFunChar c || c=='"' =  let (c,str') = readAFun str
		   	                    ((at',kids), str'')  = readParenATs at (dropSpaces str')
                                            ((at'',ann), str''') = readAnn at' (dropSpaces str'')
 			                in (addATerm (ShAAppl c kids ann) at'', str''')
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

readTAF :: ATermTable -> String -> Table -> Int -> ((ATermTable,Int),String,Table,Int)
readTAF at ('#':str) tbl l =  let (i,str') = spanAbbrevChar str
			      in (addATerm (getElement (deAbbrev i) tbl) at, 
			          str',tbl,
				  l+(length i)+1)    
readTAF at ('[':str) tbl l =  let ((at',kids), str',tbl',l') = readTAFs at ']'
                                                                  (dropSpaces str) tbl 1
                                  ((at'',ann),str'',tbl'',l'') = readAnnTAF at'
                                                                  (dropSpaces str') tbl' 0 
	                          t            = ShAList kids ann      
	                          tbl'''       = condAddElement t (l''+l') tbl''
	                          at_t         = addATerm t at''
			      in (at_t, str'',tbl''',l+l'+l'')
readTAF at str@(x:xs) tbl l 
  | isIntHead x         =  let (i,str')   = span isDigit xs
                               l'         = length (x:i)
                               ((at',ann),str'',tbl',l'') = readAnnTAF at str' tbl 0
                               t          = ShAInt (read (x:i)) ann 
	                       tbl''      = condAddElement t (l'+l'') tbl'
	                       at_t       = addATerm t at'
                           in (at_t,str'',tbl'', l+l'+l'')
  |isAFunChar x || x=='"' || x=='(' = let (c,str')           = readAFun str
		                          ((at',kids), str'',tbl',l') = readParenTAFs at
                                                                      (dropSpaces str') tbl 0
                                          ((at'',ann),str''',tbl'',l'') = readAnnTAF at'
                                                                      (dropSpaces str'') tbl' 0
			                  t                  = ShAAppl c kids ann
	                                  l'''   = (length c) + l'+l''
	                                  tbl''' = condAddElement t l''' tbl''
	                                  at_t   = addATerm t at''
 		                      in (at_t, str''',tbl''',l''')
  | otherwise             = error $ error_saterm (take 5 str)

readParenTAFs :: ATermTable -> String -> Table -> Int -> ((ATermTable,[Int]),String,Table,Int)
readParenTAFs at ('(':str) tbl l  =  readTAFs at ')'(dropSpaces str) tbl (l+1)
readParenTAFs at str       tbl l  =  ((at,[]),str,tbl,l)

readTAFs :: ATermTable -> Char -> String -> Table -> Int -> ((ATermTable,[Int]),String,Table,Int)
readTAFs at par s@(p:str) tbl l | par == p  = ((at,[]),str,tbl,l+1)
                                | otherwise = readTAFs1 at par s tbl l

readTAFs1 :: ATermTable -> Char -> String -> Table -> Int -> ((ATermTable,[Int]),String,Table,Int)
readTAFs1 at par str tbl l = let ((at',t),str',tbl',l')= readTAF at (dropSpaces str) tbl l
		                 ((at'',ts),str'',tbl'',l'') = readTAFs' at' par (dropSpaces str') tbl' l'
		             in ((at'',t:ts),str'',tbl'',l'')

readTAFs' :: ATermTable -> Char -> String -> Table -> Int -> ((ATermTable,[Int]),String,Table,Int)
readTAFs' at par (',':str) tbl l = readTAFs1 at par (dropSpaces str) tbl (l+1)
readTAFs' at par s@(p:str) tbl l | par == p  = ((at,[]),str,tbl,l+1)
                                 | otherwise = error $ error_paren (take 5 s)

readAnnTAF :: ATermTable -> String -> Table -> Int -> ((ATermTable,[Int]),String,Table,Int)
readAnnTAF at ('{':str) tbl l = readTAFs at '}' (dropSpaces str) tbl (l+1) 
readAnnTAF at str       tbl l = ((at,[]),str,tbl,l)


-- helpers --

dropSpaces :: String -> String 
dropSpaces		= dropWhile isSpace

spanAFunChar :: String -> (String,String)
spanAFunChar		= span isAFunChar

isAFunChar :: Char -> Bool
isAFunChar c		= (isAlphaNum c) || (c `elem` "-_*+")


spanNotQuote :: String -> (String,String)
spanNotQuote 		= span (/='"')

spanAbbrevChar :: String -> (String,String)
spanAbbrevChar		= span (`elem` toBase64)

isIntHead :: Char -> Bool
isIntHead c		= (isDigit c) || (c=='-')

quote :: String -> String
quote str		= ('"':str)++"\""

spanNotQuote' :: String -> (String,String)
spanNotQuote' []		= ([],[])
spanNotQuote' xs@('"':xs')  	= ([],xs)
spanNotQuote' xs@('\\':'"':xs')	= ('\\':'"':ys,zs) 
                                  where (ys,zs) = spanNotQuote' xs'
spanNotQuote' xs@(x:xs')	= (x:ys,zs) 
                                  where (ys,zs) = spanNotQuote' xs'
{-
span :: (a -> Bool) -> [a] -> ([a],[a])
span p []            = ([],[])
span p xs@(x:xs')
	 | p x       = (x:ys, zs)
	 | otherwise = ([],xs)
                       where (ys,zs) = span p xs'
-}

condAddElement :: ShATerm -> Int -> Table -> Table
condAddElement t l tbl = 
    if length (next_abbrev tbl) < l then
       addElement t tbl
    else
       tbl


--- From ATerm to String  -----------------------------------------------------

data ShowS_len = ShowS_len { showFun :: ShowS
                           , showLen :: !Int
                           } 

--type ShowS = String -> String

writeATerm :: ATermTable -> String
writeATerm at           = writeAT at $ ""

writeSharedATerm :: ATermTable -> String 
writeSharedATerm at	= let (ShowS_len{ showFun=sf },_) = writeTAF at emptyTable in '!':(sf "") 

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
   
writeAT' :: ATermTable -> [Int] -> [ShowS]
writeAT' at []     = []
writeAT' at (i:is) = let (at',t) = getATermByIndex i at 
			 str = writeAT at'
			 strs = writeAT' at is
		     in (str:strs)    
		 	    	 		    
		      
--shared--
writeTAF :: ATermTable -> Table	-> (ShowS_len,Table)
writeTAF at tbl =  
    case indexOf t tbl of
	     (Just i) -> (ShowS_len{ showFun = showString abb, showLen = length abb} , tbl) where abb = abbrev i
	     Nothing  -> (showS,condAddElement t (showLen showS) tbl') 
    where (showS,tbl') = writeTAF' at tbl
          t = getATerm at

writeTAF' :: ATermTable -> Table -> (ShowS_len,Table)
writeTAF' at tbl = 
    case getATerm at of
	     (ShAAppl c ts as) -> let (kids,tbl') = writeTAFs at ts tbl
                                      (kidsAnn,tbl'') = writeTAFs at as tbl'
                                  in ( showSConcat (writeATermAuxS c kids) (writeParenthesiseAnnS kidsAnn), tbl'') 
	     (ShAList ts as)   -> let (kids,tbl') = writeTAFs at ts tbl
				      (kidsAnn,tbl'') = writeTAFs at as tbl'
			          in (showSConcat (bracketS (commaSepS kids)) (writeParenthesiseAnnS kidsAnn) , tbl'')
	     (ShAInt i as)     -> let (kidsAnn,tbl') = writeTAFs at as tbl
		                  in (showSConcat (ShowS_len{ showFun=showString istr , showLen=length istr }) (writeParenthesiseAnnS kidsAnn) , tbl') 
				  where istr = show i

showSConcat :: ShowS_len -> ShowS_len -> ShowS_len		
showSConcat s1 s2 = ShowS_len{ showFun=(showFun s1) . (showFun s2) , showLen= (showLen s1) + (showLen s2)}

writeTAFs :: ATermTable -> [Int] -> Table -> ([ShowS_len],Table)
writeTAFs at [] tbl	=  ([],tbl)
writeTAFs at (i:is) tbl = let (at',t) = getATermByIndex i at
                              (str,tbl') = writeTAF at' tbl
			      (strs,tbl'') = writeTAFs at is tbl'
			  in (str:strs , tbl'')

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

writeATermAuxS :: String -> [ShowS_len] -> ShowS_len
writeATermAuxS c []	=  ShowS_len {showFun = showString c, showLen=length c }
writeATermAuxS c ts	=  ShowS_len {showFun = showString c . (showFun s) , showLen = length c + (showLen s) }
			   where s = parenthesiseS (commaSepS ts)

writeParenthesiseAnn :: [ShowS] -> ShowS
writeParenthesiseAnn [] = showString ""
writeParenthesiseAnn as = parenthesiseAnn $ commaSep as

writeParenthesiseAnnS :: [ShowS_len] ->  ShowS_len
writeParenthesiseAnnS [] = ShowS_len{ showFun=id , showLen=0 }
writeParenthesiseAnnS as = parenthesiseAnnS (commaSepS as)

commaSep :: [ShowS] -> ShowS
commaSep [] = showString ""
commaSep str = foldl1 (\x y-> x . showChar ',' . y) str

commaSepS :: [ShowS_len] -> ShowS_len
commaSepS []             = ShowS_len{ showFun=id , showLen=0 }
commaSepS strs	        = foldl1 eval strs
                          
eval :: ShowS_len -> ShowS_len -> ShowS_len			  
eval s1 s2 = ShowS_len{ showFun=(showFun s1) . showChar ',' . (showFun s2), showLen= 1 + (showLen s1) + (showLen s2) }
                       
bracket, parenthesise, parenthesiseAnn :: ShowS -> ShowS 
bracket         str = showChar '[' . str . showChar ']'
parenthesise    str = showChar '(' . str . showChar ')'
parenthesiseAnn str = showChar '{' . str . showChar '}'

bracketS, parenthesiseS, parenthesiseAnnS :: ShowS_len -> ShowS_len 
bracketS         s = s{ showFun=showChar '[' . (showFun s) . showChar ']',showLen=(showLen s)+2 }
parenthesiseS    s = s{ showFun=showChar '(' . (showFun s) . showChar ')',showLen=(showLen s)+2 }
parenthesiseAnnS s = s{ showFun=showChar '{' . (showFun s) . showChar '}',showLen=(showLen s)+2 }

--- Tables of ATerms ----------------------------------------------------------

type Table		=  ATermTable
emptyTable		=  emptyATermTable

indexOf :: ShATerm -> Table -> Maybe Int
indexOf t tbl           =  case getATermIndex t tbl of
			   (-1) -> Nothing
			   i    -> Just i

lengthTable :: Table -> Int
lengthTable (_,_,i)     =  i

addElement :: ShATerm -> Table -> ATermTable
addElement t tbl	=  addATerm1 t tbl

getElement :: Int -> Table -> ShATerm
getElement i tbl	=  let (_,t)    = getATermByIndex i tbl in t
 

(!!!)              :: [b] -> Integer -> b
(x:_)  !!! 0       =  x
(_:xs) !!! n | n>0 =  xs !!! (n-1)
(_:_)  !!! _       =  error "!!!: negative index"
[]     !!! _       =  error "!!!: index too large"

--- Base 64 encoding ----------------------------------------------------------

mkAbbrev :: Int -> [Char]
mkAbbrev x
  | x == 0	= [toBase64!!0]
  | otherwise   = reverse (mkAbbrevAux x)

mkAbbrevAux :: Int -> [Char]
mkAbbrevAux x
  | x == 0	= []
  | x > 0	= (toBase64!!m:mkAbbrevAux d) where (d,m) = divMod x 64

deAbbrev :: [Char] -> Int
deAbbrev x		=  deAbbrevAux (reverse x)

deAbbrevAux :: [Char] -> Int
deAbbrevAux []		=  0
deAbbrevAux (c:cs)	=  let i = base64Array ! c
               	               r = deAbbrevAux cs
			   in (i + 64*r)

base64Array :: Array Char Int
base64Array = array ('+','z') $ zip toBase64 integerList
    where integerList :: [Int]
	  integerList = [0..63]

toBase64 =
  [ 'A','B','C','D','E','F','G','H','I','J','K','L','M','N','O','P',
    'Q','R','S','T','U','V','W','X','Y','Z','a','b','c','d','e','f',
    'g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v',
    'w','x','y','z','0','1','2','3','4','5','6','7','8','9','+','/' 
  ]

-- helpers --

abbrev :: Int -> [Char]
abbrev i = '#' : (mkAbbrev i)

next_abbrev :: Table -> [Char]
next_abbrev tbl = abbrev ((lengthTable tbl)+1)



-- error messages --------------------

error_paren (s:str) = "Can't parse '" ++ [s] ++ "',expecting \",\" or matching parenthesis \nFollowing characters are:" ++ str  
error_aterm (s:str) = "Can't parse '" ++ [s] ++ "', expecting ATermAppl, ATermList or ATermInt\nFollowing characters are:" ++ str
error_saterm (s:str) = "Can't parse '" ++ [s] ++ "', expecting Abbreviate, ATermAppl, ATermList or ATermInt\nFollowing characters are:" ++ str





































