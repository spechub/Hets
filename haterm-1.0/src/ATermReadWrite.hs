module ATermReadWrite (

	readATerm,
	writeATerm,
	writeSharedATerm,

	module ATermAbstractSyntax

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

import ATermAbstractSyntax

-- added by KL
import Char

--- From String to ATerm ------------------------------------------------------

readATerm ('!':str)	= let (t,_,_) = readTAF str [] in t
readATerm str		= let (t,_)   = readAT str     in t

                                                               -- non-shared --

readAT ('[':str)	=  let (kids, str') = readATs (dropSpaces str)
			   in (AList kids, str')
readAT str@(c:cs)
  | isIntHead c		=  let (i,str') = span isDigit cs
                           in (AInt (read (c:i)),str')
  | otherwise		=  let (c,str')      = readAFun str
		   	       (kids, str'') = readParenATs  (dropSpaces str')
 			   in (AAppl c kids, str'')

readAFun ('"':str)	=  let (c,('"':str')) = spanNotQuote' str 
                           in (quote c,str')
readAFun str		=  spanAFunChar str

readParenATs ('(':str)	=  readATs (dropSpaces str)
readParenATs str	=  ([],str)


readATs (')':str)	=  ([],str)
readATs (']':str)	=  ([],str)
readATs str		=  readATs1 str

readATs1 str		=  let (t,str')   = readAT (dropSpaces str)
			       (ts,str'') = readATs' (dropSpaces str')
			   in (t:ts,str'')

readATs' (',':str)	= readATs1 (dropSpaces str)
readATs' (')':str)	= ([],str)
readATs' (']':str)	= ([],str)

                                                                   -- shared --

readTAF ('#':str) tbl	=  let (i,str') = spanAbbrevChar str
			   in (getElement (deAbbrev i) tbl, str',tbl)    
readTAF ('[':str) tbl	=  let (kids, str',tbl') = readTAFs 
                                                      (dropSpaces str) tbl
			       t                 = AList kids
 			   in (t, str',addElement t tbl')
readTAF str tbl		=  let (c,str')           = readAFun str
		   	       (kids, str'',tbl') = readParenTAFs 
                                                      (dropSpaces str') tbl
			       t                  = AAppl c kids
 			   in (t, str'',addElement t tbl')

readParenTAFs ('(':str)	tbl	=  readTAFs (dropSpaces str) tbl
readParenTAFs str tbl		=  ([],str,tbl)

readTAFs (')':str) tbl	=  ([],str,tbl)
readTAFs (']':str) tbl	=  ([],str,tbl)
readTAFs str tbl	=  readTAFs1 str tbl

readTAFs1 str tbl	=  let (t,str',tbl')    = readTAF (dropSpaces str) tbl
			       (ts,str'',tbl'') = readTAFs' 
                                                    (dropSpaces str') tbl'
			   in (t:ts,str'',tbl'')

readTAFs' (',':str) tbl	= readTAFs1 (dropSpaces str) tbl
readTAFs' (')':str) tbl	= ([],str,tbl)
readTAFs' (']':str) tbl	= ([],str,tbl)

                                                                  -- helpers --

dropSpaces		= dropWhile isSpace
spanAFunChar		= span isAFunChar
isAFunChar c		= (isAlphaNum c) || (c `elem` "-_*+")
spanNotQuote 		= span (/='"')
spanAbbrevChar		= span (`elem` toBase64)
isIntHead c		= (isDigit c) || (c=='-')
quote str		= ('"':str)++"\""

spanNotQuote' []		= ([],[])
spanNotQuote' xs@('"':xs')  	= ([],xs)
spanNotQuote' xs@('\\':'"':xs')	= ('\\':'"':ys,zs) 
                                  where (ys,zs) = spanNotQuote' xs'
spanNotQuote' xs@(x:xs')	= (x:ys,zs) 
                                  where (ys,zs) = spanNotQuote' xs'

{-
span p []            = ([],[])
span p xs@(x:xs')
	 | p x       = (x:ys, zs)
	 | otherwise = ([],xs)
                       where (ys,zs) = span p xs'
-}

--- From ATerm to String  -----------------------------------------------------

writeATerm t            = writeAT t
writeSharedATerm t	= let (s,_) = writeTAF t [] in s
                                                               -- non-shared --

writeAT 		:: ATerm -> String
writeAT (AAppl c ts)	=  writeATermAux c (map writeAT ts)
writeAT (AList ts)	=  bracket (commaSep (map writeAT ts))
writeAT (AInt i)	=  show i

                                                                   -- shared --

writeTAF		:: ATerm -> Table -> (String,Table)
writeTAF t tbl		=  case indexOf t tbl of
				(Just i) -> if (length abbrev) < (length str)
                                            then (abbrev,tbl)
                                            else (str, addElement t tbl') 
				              where abbrev = "#"++mkAbbrev i
				Nothing  -> (str, addElement t tbl')
                           where (str,tbl') = writeTAF' t tbl

writeTAF' (AAppl c ts) tbl	= let (kids,tbl') = writeTAFs ts tbl
           			  in (writeATermAux c kids,tbl')
writeTAF' (AList ts) tbl	= let (kids,tbl') = writeTAFs ts tbl
				  in (bracket (commaSep kids),tbl')
writeTAF' (AInt i) tbl		= (show i,tbl)

writeTAFs [] tbl		=  ([],tbl)
writeTAFs (t:ts) tbl	=  let (str,tbl')   = writeTAF t tbl
			       (strs,tbl'') = writeTAFs ts tbl'
			   in ((str:strs),tbl'')

                                                                  -- helpers --
 
writeATermAux c []	=  c
writeATermAux c ts	=  c++(parenthesise (commaSep ts))

sepBy sep (x:y:ys)	=  x:sep:sepBy sep (y:ys)
sepBy sep ys            =  ys

commaSep strs		=  concat (sepBy "," strs)
bracket str		= "["++str++"]"
parenthesise str	= "("++str++")"

--- Tables of ATerms ----------------------------------------------------------

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

--- Base 64 encoding ----------------------------------------------------------

mkAbbrev x
  | x == 0	= [toBase64!!0]
  | otherwise   = reverse (mkAbbrevAux x)

mkAbbrevAux x
  | x == 0	= []
  | x > 0	= (toBase64!!!m:mkAbbrevAux d) where (d,m) = divMod x 64

deAbbrev x		=  deAbbrevAux (reverse x)

deAbbrevAux []		=  0
deAbbrevAux (c:cs)	=  let (Just i) = indexOf c toBase64
               	               r        = deAbbrevAux cs
			   in (i + 64*r)

toBase64 =
  [ 'A','B','C','D','E','F','G','H','I','J','K','L','M','N','O','P',
    'Q','R','S','T','U','V','W','X','Y','Z','a','b','c','d','e','f',
    'g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v',
    'w','x','y','z','0','1','2','3','4','5','6','7','8','9','+','/' 
  ]

-------------------------------------------------------------------------------
