{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

-}

module Common.ATerm.ReadWrite (

	readATerm,       -- :: String -> ATermTable
	writeATerm,      -- :: ATermTable -> String
	writeSharedATerm,-- :: ATermTable -> String
	writeSharedATermSDoc -- :: ATermTable -> SDoc  
--	,module Common.ATerm.ReadWrite
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
import qualified Common.DFiniteMap as IntMap
import Common.SimpPretty

--import Debug.Trace
-- import Numeric don't use showInt: can't show negative numbers

--- From String to ATerm ------------------------------------------------------

data ReadTAFStruct = RTS (ATermTable,Int)
		         -- ATermTable with Index of read and added ATerm
		         String 
			 -- remaing part of the ATerm as String
			 ReadTable
			 {-#UNPACK#-}!Int -- length of ATerm as String 
		   | RTS_list (ATermTable,[Int])
		              -- ATermTable with Indices 
			      -- of read and added ATerms
		     String 
		     -- remaing part of the ATerm as String
		     ReadTable
		     {-#UNPACK#-}!Int -- length of ATerms as String 

readATerm :: String -> ATermTable 
readATerm ('!':str)	= 
    case readTAF emptyATermTable str emptyRTable 0 of
    (RTS (at,_) _ _rt _l) -> at
{-	ab = case rt of
	     RTab _ i -> ("Read: next_abbrev="++show i
			  ++" ATT-TopIndex="++show (getTopIndex at)
			  ++" length-of-aterm="++show l)-}
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
readAFun ('"':str)	=  let (c, str') = spanNotQuote' str 
                           in ('"': c, str')
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
	-> ReadTable -> Int -> ReadTAFStruct
readTAF at ('#':str) tbl l =  
    case {-# SCC "spanAbbrevChar" #-} spanAbbrevChar str of
    (i,str') -> {-# SCC "RTS_abb" #-}  
          RTS (at,getATermIndex (getAbbrevTerm (deAbbrev i) at tbl) at)
                                str' tbl (l+(length i)+1)    
readTAF at ('[':str) tbl l =  
	case {-# SCC "RTAFs_AList" #-} 
             readTAFs at ']' (dropSpaces str) tbl 1 of
        (RTS_list (at' ,kids) str'  tbl'  l') -> 
          case 
	    readAnnTAF at' (dropSpaces str') tbl' 0 of
	  (RTS_list (at'',ann)  str'' tbl'' l'') ->
           case {-# SCC "Cons_AList" #-} ShAList kids ann of
	   t -> case  {-# SCC "RaddAList" #-} addATermNoFullSharing t at'' of
		at_t@(_,ai) -> 
                 case {-# SCC "RaddAListAbbr" #-}  
		  seq ai (condAddElement next_abbrev_R_len 
                                         (addRAbbrev ai) (l''+l') tbl'') of
		 tbl''' -> {-# SCC "RTS_AList" #-} 
		       RTS at_t str'' tbl''' (l+l'+l'')
readTAF at str@(x:xs) tbl l 
  | isIntHead x =  
     case {-# SCC "RspanDigits" #-} span isDigit xs of
     (i,str') -> 
         case readAnnTAF at str' tbl 0 of
	 (RTS_list (at',ann) str'' tbl' l'') ->
	   case {-# SCC "Rread_integer" #-} readInteger (x:i) of
	   (integer, l') ->
	    case {-# SCC "RaddAInt" #-} 
	       addATermNoFullSharing (ShAInt integer ann) at' of
	    at_t@(_,ai) ->
              case {-# SCC "RaddAIntAbbrev" #-}  
	         seq ai (condAddElement next_abbrev_R_len 
			                (addRAbbrev ai) (l'+l'') tbl') of
	      tbl'' -> {-# SCC "RTS_AInt" #-} RTS at_t str'' tbl'' (l+l'+l'')
  | isAlphaNum x || x=='"' || x=='(' || x == '_' || x == '*' || x == '+' = 
     case {-# SCC "RspanConstructor" #-} readAFun str of
     (c,str') ->
       case {-# SCC "RTAFs_AAppl" #-} 
            readParenTAFs at (dropSpaces str') tbl 0 of
       (RTS_list (at',kids) str'' tbl' l') ->
         case readAnnTAF at' (dropSpaces str'') tbl' 0 of
	 (RTS_list (at'',ann) str''' tbl'' l'') ->
	   case {-# SCC "RaddAAppl" #-} 
		addATermNoFullSharing (ShAAppl c kids ann) at'' of
	   at_t@(_,ai) ->
             case ((length c) + l'+l'') of
	     l''' -> seq l''' 
              (case {-# SCC "RaddAApplAbbrev" #-} 
		  seq ai (condAddElement next_abbrev_R_len 
                                         (addRAbbrev ai) l''' tbl'') of
	       tbl''' -> {-# SCC "RTS_AAppl" #-} 
                    RTS at_t str''' tbl''' l''')
  | otherwise             = error $ error_saterm (take 5 str)

readParenTAFs :: ATermTable -> String -> ReadTable 
	      -> Int -> ReadTAFStruct
readParenTAFs at ('(':str) tbl l  =  readTAFs at ')'(dropSpaces str) tbl (l+1)
readParenTAFs at str       tbl l  =  RTS_list (at,[]) str tbl l

readTAFs :: ATermTable -> Char -> String -> ReadTable 
	 -> Int -> ReadTAFStruct
readTAFs at par s@(p:str) tbl l | par == p  = RTS_list (at,[]) str tbl (l+1)
                                | otherwise = readTAFs1 at par s tbl l

readTAFs1 :: ATermTable -> Char -> String -> ReadTable -> Int 
	  -> ReadTAFStruct
readTAFs1 at par str tbl l = 
    case  readTAF at (dropSpaces str) tbl l of
    (RTS (at' ,t)  str'  tbl'  l') -> 
      case readTAFs' at' par (dropSpaces str') tbl' l' of
      (RTS_list (at'',ts) str'' tbl'' l'') ->	 
              (RTS_list (at'',t:ts) str'' tbl'' l'') 

readTAFs' :: ATermTable -> Char -> String -> ReadTable -> Int 
			-> ReadTAFStruct
readTAFs' at par (',':str) tbl l = readTAFs1 at par (dropSpaces str) tbl (l+1)
readTAFs' at par s@(p:str) tbl l | par == p  = RTS_list (at,[]) str tbl (l+1)
                                 | otherwise = error $ error_paren (take 5 s)

readAnnTAF :: ATermTable -> String -> ReadTable -> Int 
	   -> ReadTAFStruct
readAnnTAF at ('{':str) tbl l = readTAFs at '}' (dropSpaces str) tbl (l+1) 
readAnnTAF at str       tbl l = (RTS_list (at,[]) str tbl l)


-- helpers --

dropSpaces :: String -> String 
dropSpaces		= dropWhile isSpace

spanAFunChar :: String -> (String,String)
spanAFunChar		= span isAFunChar

isAFunChar :: Char -> Bool
isAFunChar c = isAlphaNum c || c == '_' || c == '*' || c == '+' ||  c == '-'

spanAbbrevChar :: String -> (String,String)
spanAbbrevChar		= span isBase64Char

isIntHead :: Char -> Bool
isIntHead c		= (isDigit c) || (c=='-')

spanNotQuote' :: String -> (String,String)
spanNotQuote' []		= error "spanNotQuote'"
spanNotQuote' ('"':xs')  	= ("\"",xs')
spanNotQuote' ('\\':c:xs')	= case spanNotQuote' xs' of
                                  (ys,zs) -> ('\\':c:ys,zs) 
spanNotQuote' (x:xs')	= case spanNotQuote' xs' of
			       (ys,zs) -> (x:ys,zs) 

{-
span :: (a -> Bool) -> [a] -> ([a],[a])
span p []            = ([],[])
span p xs@(x:xs')
	 | p x       = (x:ys, zs)
	 | otherwise = ([],xs)
                       where (ys,zs) = span p xs'
-}

{-# SPEZIALIZE condAddElement :: (WriteTable -> Int) -> (WriteTable -> WriteTable) -> Int -> WriteTable -> WriteTable #-}
{-# SPEZIALIZE condAddElement :: (ReadTable -> Int) -> (ReadTable -> ReadTable) -> Int -> ReadTable -> ReadTable #-}

condAddElement :: (tab -> Int) -> (tab -> tab) -> Int -> tab -> tab
condAddElement next_abbrev_len add l tbl = 
    -- length $ abbrev (maxBound::Int) == 7, so every ATerm with a
    -- string size greater than 7 must be added
    if l>7 || (next_abbrev_len tbl) < l then
       add tbl
    else
       tbl

--- From ATerm to String  -----------------------------------------------------

-- a helper data Type for SDocs paired with the associated length
data Doc_len = Doc_len SDoc {-# UNPACK #-} !Int

data Write_struct = WS WriteTable {-# UNPACK #-} !Doc_len

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

writeSharedATermSDoc :: ATermTable -> SDoc
writeSharedATermSDoc at = 
    if getTopIndex at == -1 then fatal_error "writeSharedATermSDoc: empty"
    else case writeTAF at emptyWTable of
    WS _ (Doc_len doc l)
--    (WS (WTab _ ((Doc_len d _),i)) (Doc_len doc _)) -> 
	| isEmpty doc || l == 0 -> fatal_error "writeSharedATermSDoc"
	| otherwise ->
{-	trace ("Write: "++show d++" "
	       ++show (deAbbrev (tail . show $ d))++" "++show i) -}
		  (char '!'<>doc)

writeSharedATerm :: ATermTable -> String 
writeSharedATerm = render . writeSharedATermSDoc

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
writeTAF at tbl@(WTab ai_abb_map _) = let i = getTopIndex at in  
    case IntMap.lookup i ai_abb_map of
    Just s -> WS tbl s 
    Nothing  -> case writeTAF' at tbl of
		(WS tbl' d_len@(Doc_len _ len)) -> 
		    WS (condAddElement next_abbrev_W_len
                                (addWAbbrev i) 
		                len tbl') d_len
	  -- risking a faulty writeTAF' implementation

writeTAF' :: ATermTable -> WriteTable -> Write_struct
writeTAF' at tbl = 
    case getATerm at of
    (ShAAppl c ts as) -> 
	      case writeTAFs at ts tbl of
	      (WS tbl' kids) ->
		  case writeTAFs at as tbl' of
		  (WS tbl'' kidsAnn) ->
                     WS tbl'' $ dlConcat (writeATermAuxS c kids) 
		                         (parenthesiseAnnS kidsAnn)
    (ShAList ts as)   -> 
	      case writeTAFs at ts tbl of
	      (WS tbl' kids) ->
		  case writeTAFs at as tbl' of
		  (WS tbl'' kidsAnn) ->
		      WS tbl'' $ dlConcat (bracketS kids) 
		                          (parenthesiseAnnS kidsAnn)
    (ShAInt i as)     -> 
	case writeTAFs at as tbl of
        (WS tbl' kidsAnn) ->
		 -- don't use showInt: can't show negative numbers
	      WS tbl' $ dlConcat (Doc_len (integer i) (length (show i))) 
		                 (parenthesiseAnnS kidsAnn)

dlConcat :: Doc_len -> Doc_len -> Doc_len		
{-showSConcat ShowS_len_empty ShowS_len_empty = fatal_error "showSConcat"
showSConcat ShowS_len_empty showS_len = showS_len
showSConcat showS_len ShowS_len_empty = showS_len-}
dlConcat s1@(Doc_len sf1 sl1) s2@(Doc_len sf2 sl2) 
    | (sl1 == 0 || isEmpty sf1) 
      && (sl2 == 0 || isEmpty sf2) = fatal_error "showSConcat"
    | sl1 == 0 || isEmpty sf1 = s2 
    | sl2 == 0 || isEmpty sf2 = s1
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
    | (sl1 == 0 || isEmpty sf1) 
      && (sl2 == 0 || isEmpty sf2) = fatal_error "showSConcat"
    | sl1 == 0 || isEmpty sf1 = Doc_len (sf2 <>comma) (sl2 + 1)
    | sl2 == 0 || isEmpty sf2 = Doc_len (sf1 <>comma) (sl1 + 1)
    | otherwise = Doc_len (sf1 <> sf2 <> comma) (sl1 + sl2 + 1)


-- produce a String function with a comma seperated string converted ATerms
writeTAFs :: ATermTable -> [Int] -> WriteTable -> Write_struct
writeTAFs _  [] tbl = (WS tbl $ Doc_len empty 0)
writeTAFs at inds tbl = writeTAFs' inds (WS tbl $ Doc_len empty 0)
    where writeTAFs' :: [Int] -> Write_struct -> Write_struct
	  writeTAFs' [] _ = error "not reachable"
	  writeTAFs' [i] (WS t s) = 
	      case  wT t i of
	      (WS t' s') -> WS t' (dlConcat s s')
	  writeTAFs' (i:is) (WS t s) = 
	      case  wT t i of
	      (WS t' s') -> writeTAFs' is (WS t' (dlConcat_comma s s'))
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
writeATermAuxS c doc_len@(Doc_len d l)	 
    | l == 0 && isEmpty d = Doc_len (text c) (length c)
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
    | dl == 0 && isEmpty d = Doc_len (brackets empty) 2
    | otherwise = Doc_len (brackets d) (dl+2)
-- parenthesiseS    ShowS_len_empty   = ShowS_len_empty
parenthesiseS    s@(Doc_len d dl) 
    | dl == 0 && isEmpty d  = s
    | otherwise = Doc_len (parens d) (dl+2)
--parenthesiseAnnS ShowS_len_empty   = ShowS_len_empty
parenthesiseAnnS s@(Doc_len d dl) 
    | dl == 0 && isEmpty d = s
    | otherwise = Doc_len (braces d) (dl+2)

--- Tables of ATerms ----------------------------------------------------------

-- These Tables consist of FiniteMaps, because all ATerms are indexed
-- with an Int in the second component of the ATermTable. So
-- ATermIndex is the Index that is given by getATermIndex.

-- Map: Abbrev     -> ATermIndex
data ReadTable  = RTab (IntMap.Map Int Int) {-# UNPACK #-} !Int

-- 1st Map: ATermIndex -> Abbrev
-- TODO: implement 2nd Map as WriteCache 
--         (sf::ShowS,length of String in sf::Int) .. done
data WriteTable = WTab (IntMap.Map Int Doc_len) 
                       {-# UNPACK #-} !(Doc_len,Int)

emptyRTable :: ReadTable
emptyRTable = RTab IntMap.empty 0

emptyWTable :: WriteTable
emptyWTable = WTab IntMap.empty (abbrevD 0, 0)

{-
lengthOfShATermInd :: Int -> WriteTable -> Maybe Int
lengthOfShATermInd ai (WTab _ lmap _) = IntMap.lookup ai lmap
-}

-- top-level / selected ATerm gets next abbrev and a length
addWAbbrev :: Int -> WriteTable -> WriteTable
addWAbbrev ai (WTab ai_abb_map (da,i)) 
    | ai < 0    = error "addWAbbrev: negative index" 
    | otherwise = 
	case (IntMap.insert ai da ai_abb_map) of
	new_map -> seq new_map (
		  maybe (WTab new_map (abbrevD (i+1),i+1))
		        (error ("destructive update in WriteTable "
				++show i++" "
				++show ai))
		        (IntMap.lookup ai ai_abb_map))

-- the String Argument is not used and serves as dummy for ease of code change
addRAbbrev :: Int -> ReadTable -> ReadTable
addRAbbrev ai (RTab abb_ai_map i) 
    | ai < 0    = error "addRAbbrev: negative index" 
    | otherwise = 
	maybe (RTab (IntMap.insert i ai abb_ai_map) (i+1)) 
	      (error ("destructive update in ReadTable "++show i++" "
		      ++show ai))
	      (IntMap.lookup i abb_ai_map)

getAbbrevTerm :: Int -> ATermTable -> ReadTable -> ShATerm
getAbbrevTerm i at (RTab abb_ai_map _) =  
    case IntMap.find i abb_ai_map of
    ai -> getATerm $ getATermByIndex1 ai at 

{-
(!!!)              :: [b] -> Integer -> b
(x:_)  !!! 0       =  x
(_:xs) !!! n | n>0 =  xs !!! (n-1)
(_:_)  !!! _       =  error "!!!: negative index"
[]     !!! _       =  error "!!!: index too large"
-}
--- Intger Read ---------------------------------------------------------------

readInteger :: String -> (Integer, Int)
readInteger s@(hd:str) = if hd == '-' then case conv str of
			 (m, l) -> (negate m, l + 1)
			 else conv s
    where f (m, l) x = (toInteger (ord x - ord '0') + 10 * m, l + 1)
	  conv = foldl f (0, 0)

--- Base 64 encoding ----------------------------------------------------------

mkAbbrev :: Int -> String
mkAbbrev x
  | x > 0       = mkAbbrevAux x ""
  | x == 0	= "A"
  | otherwise   = error ("mkAbbrev: negative Int "++ show x)

mkAbbrevAux :: Int -> String -> String
mkAbbrevAux x str = 
  if x > 0 then case quotRem x 64 of 
	 (d, m) -> mkAbbrevAux d (toBase64Char m : str)
  else str

deAbbrev :: [Char] -> Int
deAbbrev =  let f m c = 64*m + toBase64Int c in foldl f 0 

{-
toBase64 :: [Char]
toBase64 =
  [ 'A','B','C','D','E','F','G','H','I','J','K','L','M','N','O','P',
    'Q','R','S','T','U','V','W','X','Y','Z','a','b','c','d','e','f',
    'g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v',
    'w','x','y','z','0','1','2','3','4','5','6','7','8','9','+','/' 
  ]
-}

toBase64Int :: Char -> Int
toBase64Int c 
    | c >= 'A' && c <= 'Z' = ord c - ord 'A'
    | c >= 'a' && c <= 'z' = ord c - ord 'a' + 26
    | isDigit c = ord c - ord '0' + 52
    | c == '+' = 62
    | c == '/' = 63
    | otherwise = error "toBase64Int"

toBase64Char :: Int -> Char
toBase64Char i
    | i < 26 = chr (ord 'A' + i)
    | i < 52 = chr (ord 'a' + i - 26)
    | i < 62 = chr (ord '0' + i - 52)
    | i == 62 = '+'
    | i == 63 = '/'
    | otherwise = error "toBase64Char"

isBase64Char :: Char -> Bool
isBase64Char c = isAscii c && (isAlphaNum c || c == '+' || c == '/')

-- helpers --
abbrevD :: Int -> Doc_len
abbrevD i = case abbrev i of
	    abbStr -> (Doc_len (text abbStr) (length abbStr))

abbrev :: Int -> [Char]
abbrev i = '#' : (mkAbbrev i)

next_abbrev_W_len :: WriteTable -> Int
next_abbrev_W_len (WTab _ (Doc_len _ len,_)) = len

next_abbrev_R_len :: ReadTable -> Int
next_abbrev_R_len (RTab _ siz) = length $ abbrev (siz)

-- error messages --------------------

error_paren (s:str) = "Can't parse '" ++ [s] ++ "',expecting \",\" or matching parenthesis \nFollowing characters are:" ++ str  
error_aterm (s:str) = "Can't parse '" ++ [s] ++ "', expecting ATermAppl, ATermList or ATermInt\nFollowing characters are:" ++ str
error_saterm (s:str) = "Can't parse '" ++ [s] ++ "', expecting Abbreviate, ATermAppl, ATermList or ATermInt\nFollowing characters are:" ++ str
