{- todo:


Testbeispiele:

writeATerm (fst (addATerm (AAppl "f" [][]) emptyATermTable))



-}
module Common.ATerm.ReadWrite (

	readATerm,
	writeATerm,
	writeSharedATerm,

	module Common.ATerm.AbstractSyntax

) where

{-
	Author: Joost Visser, CWI, 2002

	This module contains functions for reading and writing ATerms
        from and to Strings. Two ATerm formats are supported:

		AT:	plain (non-shared) textual ATerms
		TAF:	shared textual ATerms

	The binary ATerm format (BAF) is not supported.

	Current limitations:

		BLOBS and place-holders are not supported.

		Annotations are not supported.

-}

import Common.ATerm.AbstractSyntax

-- added by KL
import Data.Char

import Common.Lib.Map
import Data.List
--- From String to ATerm ------------------------------------------------------

readATerm ('!':str)	= 
    let ((at,_),_,_,_) = readTAF emptyATermTable str emptyTable 0 in at
readATerm str		= 
    let ((at,_),_)     = readAT  emptyATermTable str      in at

                                                               -- non-shared --

readAT at ('[':str)	=  let ((at',kids), str') = readATs at (dropSpaces str)
			   in (addATerm (AList kids) at', str')
readAT at str@(c:cs)
  | isIntHead c		=  let (i,str') = span isDigit cs
                           in (addATerm (AInt (read (c:i))) at,str')
  | otherwise		=  let (c',str')      = readAFun str
		   	       ((at',kids), str'') = readParenATs at 
	                                               (dropSpaces str')
 			   in (addATerm (AAppl c' kids) at', str'')
readAT _a []            =  error "empty argument: readAT _ \"\""

readAFun ('"':str)	=  let (c,('"':str')) = spanNotQuote' str 
                           in (quote c,str')
readAFun str		=  spanAFunChar str

readParenATs at ('(':str) =  readATs at (dropSpaces str)
readParenATs at str	  =  ((at,[]),str)


readATs at (')':str)	=  ((at,[]),str)
readATs at (']':str)	=  ((at,[]),str)
readATs at str		=  readATs1 at str

readATs1 at str		=  let ((at',t),str')    = readAT at (dropSpaces str)
			       ((at'',ts),str'') = readATs' at' 
						             (dropSpaces str')
			   in ((at'',t:ts),str'')

readATs' at (',':str)	= readATs1 at (dropSpaces str)
readATs' at (')':str)	= ((at,[]),str)
readATs' at (']':str)	= ((at,[]),str)
readATs' _at str        = error ("readAts' _ " ++ str)
                                                                   -- shared --

readTAF at ('#':str) tbl l =  let (i,str') = spanAbbrevChar str
			      in (addATerm (getElement (deAbbrev i) tbl) at, 
				  str',tbl,
				  l+(length i)+1)    
readTAF at ('[':str) tbl l =  let ((at',kids), str',tbl',l') = readTAFs at
                                                         (dropSpaces str) tbl 1
	                          t            = AList kids       
	                          tbl''        = condAddElement t l' tbl'
	                          at_t         = addATerm t at'
			   in (at_t, str',tbl'',l+l')
readTAF at str@(x:xs) tbl l 
  | isIntHead x         =  let (i,str')   = span isDigit xs
                               l'         = length (x:i)
                               t          = AInt (read (x:i)) 
	                       tbl'       = condAddElement t l' tbl
	                       at_t       = addATerm t at
                           in (at_t,str',tbl', l+l')
  | otherwise           =  let (c,str')           = readAFun str
		   	       ((at',kids), str'',tbl',l') = readParenTAFs at
                                                        (dropSpaces str') tbl 0
			       t                  = AAppl c kids
	                       l''    = (length c) + l'
	                       tbl''  = condAddElement t l'' tbl'
	                       at_t   = addATerm t at'
 			   in (at_t, str'',tbl'',l'')
readTAF _ [] _ _        = error "empty argument: readTAF _ \"\""

readParenTAFs at ('(':str)	tbl l	=  readTAFs at (dropSpaces str) tbl l
readParenTAFs at str tbl l		=  ((at,[]),str,tbl,l)

readTAFs at (')':str) tbl l =  ((at,[]),str,tbl,l+1)
readTAFs at (']':str) tbl l =  ((at,[]),str,tbl,l+1)
readTAFs at str tbl l       =  readTAFs1 at str tbl l

readTAFs1 at str tbl l = let ((at',t),str',tbl',l')= readTAF at 
						 (dropSpaces str) tbl l
			     ((at'',ts),str'',tbl'',l'') = readTAFs' at'
                                                 (dropSpaces str') tbl' l'
			   in ((at'',t:ts),str'',tbl'',l'')

readTAFs' at (',':str) tbl	l = readTAFs1 at (dropSpaces str) tbl (l+1)
readTAFs' at (')':str) tbl	l = ((at,[]),str,tbl,l+1)
readTAFs' at (']':str) tbl	l = ((at,[]),str,tbl,l+1)
readTAFs' _at str _ _             = error ("readTAFs' _ " ++ str)

                                                                  -- helpers --

dropSpaces		= dropWhile isSpace
spanAFunChar		= span isAFunChar
isAFunChar c		= (isAlphaNum c) || (c `elem` "-_*+")
-- spanNotQuote 		= span (/='"')
spanAbbrevChar		= span (`elem` toBase64)
isIntHead c		= (isDigit c) || (c=='-')
quote str		= ('"':str)++"\""

spanNotQuote' []		= ([],[])
spanNotQuote' xs@('"': _)  	= ([],xs)
spanNotQuote' ('\\':'"':xs')    = ('\\':'"':ys,zs) 
                                  where (ys,zs) = spanNotQuote' xs'
spanNotQuote' (x:xs')	        = (x:ys,zs) 
                                  where (ys,zs) = spanNotQuote' xs'

{-
span p []            = ([],[])
span p xs@(x:xs')
	 | p x       = (x:ys, zs)
	 | otherwise = ([],xs)
                       where (ys,zs) = span p xs'
-}

condAddElement t l tbl = 
    if length (next_abbrev tbl) < l then
       addElement t tbl
    else
       tbl

--- From ATerm to String  -----------------------------------------------------

writeATerm at           = writeAT at 
writeSharedATerm at	= let (s,_) = writeTAF at emptyTable in '!':s
                                                               -- non-shared --

writeAT        :: ATermTable -> String
writeAT at     =  
    case (getATerm at) of
	     (AAppl c ts) -> writeATermAux c (writeAT' at ts)  
	     (AList ts)   -> bracket (commaSep (writeAT' at ts)) 
	     (AInt i)     -> (show i)
	     (AIndex _)   -> error err_wrong_store

writeAT' _at []    = []
writeAT' at (t:ts) = 
    case t of 
    (AIndex i) -> let (at',t')   = getATermByIndex i at
		      str = case t' of
			    (AIndex _) -> error err_ref_index
			    _  -> writeAT at'
		      strs = writeAT' at ts
		  in str:strs
    _ -> error err_wrong_store
  						                   -- shared --

writeTAF :: ATermTable -> Table	-> (String,Table)
writeTAF at tbl =  
    case indexOf t tbl of
	     (Just i) -> (abbrev i,tbl)
	     Nothing  -> (str,
			  condAddElement t
				         (length str) 
				         tbl') 
		  where (str,tbl') = writeTAF' at tbl
    where t = getATerm at

writeTAF' at tbl = 
    case getATerm at of
	     (AAppl c ts) -> let (kids,tbl') = writeTAFs at ts tbl
           		     in (writeATermAux c kids,tbl')
	     (AList ts)   -> let (kids,tbl') = writeTAFs at ts tbl
			     in (bracket (commaSep kids),tbl')
	     (AInt i)     -> (show i,tbl)
	     (AIndex _)   -> error err_wrong_store

writeTAFs _at [] tbl	=  ([],tbl)
writeTAFs at (t:ts) tbl =  
    case t of
    (AIndex i) -> let (at',t')   = getATermByIndex i at
		      (str,tbl') = case t' of
				   (AIndex _) -> error err_ref_index
				   _  -> writeTAF at' tbl
		      (strs,tbl'') =  writeTAFs at ts tbl'
		  in ((str:strs),tbl'')
    _ -> error err_wrong_store

                                                                  -- helpers --
 
writeATermAux c []	=  c
writeATermAux c ts	=  c++(parenthesise (commaSep ts))

sepBy sep (x:y:ys)	=  x:sep:sepBy sep (y:ys)
sepBy _sep ys           =  ys

commaSep strs		=  concat (sepBy "," strs)
bracket str		= "["++str++"]"
parenthesise str	= "("++str++")"

--- Tables of ATerms ----------------------------------------------------------

type Table		=  ATermTable
emptyTable		=  emptyATermTable
indexOf t tbl           =  case getATermIndex t tbl of
			   (-1) -> Nothing
			   i    -> Just i

lengthTable (_,_,i)     =  i

addElement t tbl	=  addATerm1 t tbl
getElement i tbl	=  let (_,t)    = getATermByIndex i tbl in t
 
{-
type Table		=  [ATerm]
emptyTable		=  []
indexOf t []		=  Nothing
indexOf t (x:xs)	=  if t==x
                           then (Just (0::Integer))
                           else case indexOf t xs of
				 (Just i)   -> Just (i+1)
				 Nothing    -> Nothing
addElement t tbl	=  tbl++[t]
getElement i tbl	=  tbl!!!i

(!!!)              :: [b] -> Integer -> b
(x:_)  !!! 0       =  x
(_:xs) !!! n | n>0 =  xs !!! (n-1)
(_:_)  !!! _       =  error "!!!: negative index"
[]     !!! _       =  error "!!!: index too large"
-}
--- Base 64 encoding ----------------------------------------------------------

mkAbbrev x
  | x == 0	= [toBase64!!0]
  | otherwise   = reverse (mkAbbrevAux x)

mkAbbrevAux x
  | x == 0	= []
  | x > 0	= let (d,m) = divMod x 64 in (toBase64!!m:mkAbbrevAux d)
  | otherwise   = error ("negativ index: mkAbbrevAux " ++ show x)

deAbbrev x		=  deAbbrevAux (reverse x)

deAbbrevAux []		=  0
deAbbrevAux (c:cs)	=  let (Just i) = elemIndex c toBase64
               	               r        = deAbbrevAux cs
			   in (i + 64*r)

toBase64 =
  [ 'A','B','C','D','E','F','G','H','I','J','K','L','M','N','O','P',
    'Q','R','S','T','U','V','W','X','Y','Z','a','b','c','d','e','f',
    'g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v',
    'w','x','y','z','0','1','2','3','4','5','6','7','8','9','+','/' 
  ]

-- helpers --

abbrev i = '#':mkAbbrev i

next_abbrev tbl = abbrev ((lengthTable tbl)+1)

-------------------------------------------------------------------------------
