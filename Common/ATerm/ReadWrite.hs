{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, C.Maeder, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

-}

module Common.ATerm.ReadWrite (

        readATerm,       -- :: String -> ATermTable
        writeATerm,      -- :: ATermTable -> String
        writeSharedATerm,-- :: ATermTable -> String
        writeSharedATermSDoc -- :: ATermTable -> SDoc  
) where

{-
        Author: Joost Visser, CWI, 2002
        Changed by: Klaus Luettich & Felix Reckers, 2002-2003

        This module contains functions for reading and writing ATerms
        from and to Strings. Two ATerm formats are supported:

                AT:     plain (non-shared) textual ATerms
                TAF:    shared textual ATerms

        The binary ATerm format (BAF) is not supported.

        Current limitations:

                BLOBS and place-holders are not supported.

                

-}

import Common.ATerm.AbstractSyntax

import Data.Char
import qualified Common.Lib.Map as Map -- used with Int keys only
import Common.SimpPretty

--- From String to ATerm ------------------------------------------------------

data ReadTAFStruct = RTS ATermTable
                         -- ATermTable
                         String 
                         -- remaing part of the ATerm as String
                         ReadTable
                         Int -- length of ATerm as String 

readATerm :: String -> ATermTable 
readATerm ('!':str)     = 
    case readTAF emptyATermTable str emptyRTable 0 of
    (RTS at _ _rt _l, _) -> toReadonlyATT at
readATerm str           = 
    fst $ fst $ readAT emptyATermTable (dropSpaces str)


-- non-shared --

readAT :: ATermTable -> String -> ((ATermTable,Int),String)
readAT at ('[':str)        =  let ((at',kids), str') = readATs at ']' 
                                                       (dropSpaces str)
                                  ((at'',ann), str'')= readAnn at' 
                                                       (dropSpaces str')
                              in (addATerm (ShAList kids ann) at'', str'')
readAT at str@(c:cs)
  | isIntHead c            =  let (i,str') = span isDigit cs
                                  ((at',ann), str'') = readAnn at 
                                                       (dropSpaces str')
                              in (addATerm (ShAInt (read (c:i)) ann) at',str'')
  | c=='(' || isAFunChar c || c=='"' =  
             let (c',str') = readAFun str
                 ((at',kids), str'')  = readParenATs at (dropSpaces str')
                 ((at'',ann), str''') = readAnn at' (dropSpaces str'')
             in (addATerm (ShAAppl c' kids ann) at'', str''')
  | otherwise              = error $ error_aterm (take 6 str) 
readAT _ []                = error "readATerm: empty string"  


readAFun :: String -> (String,String)
readAFun ('"':str)      =  let (c, str') = spanNotQuote' str 
                           in ('"' : c, str')
readAFun str            =  spanAFunChar str

readParenATs :: ATermTable -> String -> ((ATermTable,[Int]),String)
readParenATs at ('(':str) =  readATs at ')' (dropSpaces str)
readParenATs at str       =  ((at,[]),str)

readATs :: ATermTable -> Char -> String -> ((ATermTable,[Int]),String)
readATs at par s@(p:str)  | par == p   = ((at,[]),str)
                          | otherwise  = readATs1 at par s
readATs _ _ [] = error "readATs: empty string"

readATs1 :: ATermTable -> Char -> String -> ((ATermTable,[Int]),String) 
readATs1 at par str     =  let ((at',t),str')    = readAT   at  
                                                   (dropSpaces str)
                               ((at'',ts),str'') = readATs' at' par 
                                                   (dropSpaces str')
                           in ((at'',t:ts),str'')

readATs' :: ATermTable -> Char -> String -> ((ATermTable,[Int]),String) 
readATs' at par (',':str)  = readATs1 at par (dropSpaces str)
readATs' at par s@(p:str)  | par == p  = ((at,[]),str)
                           | otherwise = error (error_paren (take 6 s))
readATs' _ _ [] = error "readATs': empty string"

readAnn :: ATermTable -> String -> ((ATermTable,[Int]),String)
readAnn at ('{':str) = readATs at '}' (dropSpaces str)
readAnn at str       = ((at,[]),str) 


-- shared --

readTAF :: ATermTable -> String 
        -> ReadTable -> Int -> (ReadTAFStruct, Int)
readTAF at str@(x:xs) tbl l 
  | x == '#' =
    case spanAbbrevChar xs of
    (i,str') -> (RTS at str' tbl (l+(length i)+1), 
           getATermIndex (getAbbrevTerm (deAbbrev i) at tbl) at)    
  | x == '[' =
        case readTAFs at ']' (dropSpaces xs) tbl 1 of
        (RTS at' str'  tbl'  l', kids) -> 
          case readAnnTAF at' (dropSpaces str') tbl' 0 of
          (RTS at'' str'' tbl'' l'', ann)  -> 
           case addATermNoFullSharing (ShAList kids ann) at'' of
                (at_t, ai) -> let l''' = l''+l' in
                       (RTS at_t str'' (condAddRElement ai l''' tbl'') 
                        (l + l'''), ai)
  | isIntHead x =  
     case span isDigit xs of
     (i,str') -> 
         case readAnnTAF at str' tbl 0 of
         (RTS at' str'' tbl' l'', ann) ->
           case readInteger (x:i) of
           (intl, l') ->
            case addATermNoFullSharing (ShAInt intl ann) at' of
            (at_t, ai) -> let l''' = l''+l' in
              (RTS at_t str'' (condAddRElement ai l''' tbl') (l + l'''), ai)
  | isAlpha x || x=='"' || x=='(' || x == '_' || x == '*' || x == '+' = 
     case readAFun str of
     (c,str') ->
       case readParenTAFs at (dropSpaces str') tbl 0 of
       (RTS at' str'' tbl' l', kids) ->
         case readAnnTAF at' (dropSpaces str'') tbl' 0 of
         (RTS at'' str''' tbl'' l'', ann) ->
           case addATermNoFullSharing (ShAAppl c kids ann) at'' of
           (at_t,ai) -> let l''' = l' + l''+ length c in
              (RTS at_t str''' (condAddRElement ai l''' tbl'') (l + l'''), ai)
  | otherwise             = error $ error_saterm (take 6 str)
readTAF _ [] _ _ = error "readTAF: empty string"

readParenTAFs :: ATermTable -> String -> ReadTable 
              -> Int -> (ReadTAFStruct, [Int])
readParenTAFs at ('(':str) tbl l  =  readTAFs at ')'(dropSpaces str) tbl (l+1)
readParenTAFs at str       tbl l  =  (RTS at str tbl l, [])

readTAFs :: ATermTable -> Char -> String -> ReadTable 
         -> Int -> (ReadTAFStruct, [Int])
readTAFs at par s@(p:str) tbl l | par == p  = (RTS at str tbl (l+1), [])
                                | otherwise = readTAFs1 at par s tbl l
readTAFs _ _ [] _ _ = error "readTAFs: empty string"

readTAFs1 :: ATermTable -> Char -> String -> ReadTable -> Int 
          -> (ReadTAFStruct, [Int])
readTAFs1 at par str tbl l = 
    case  readTAF at (dropSpaces str) tbl l of
    (RTS at' str'  tbl'  l' , t) -> 
      case readTAFs' at' par (dropSpaces str') tbl' l' of
      (RTS at'' str'' tbl'' l'', ts) ->  
              (RTS at'' str'' tbl'' l'', t:ts) 

readTAFs' :: ATermTable -> Char -> String -> ReadTable -> Int 
                        -> (ReadTAFStruct, [Int])
readTAFs' at par (',':str) tbl l = readTAFs1 at par (dropSpaces str) tbl (l+1)
readTAFs' at par s@(p:str) tbl l | par == p  = (RTS at str tbl (l+1), [])
                                 | otherwise = error $ error_paren (take 6 s)
readTAFs' _ _ [] _ _ = error "readTAFs': empty string"

readAnnTAF :: ATermTable -> String -> ReadTable -> Int 
           -> (ReadTAFStruct, [Int])
readAnnTAF at ('{':str) tbl l = readTAFs at '}' (dropSpaces str) tbl (l+1) 
readAnnTAF at str       tbl l = (RTS at str tbl l, [])


-- helpers --

dropSpaces :: String -> String 
dropSpaces              = dropWhile isSpace

spanAFunChar :: String -> (String,String)
spanAFunChar            = span isAFunChar

isAFunChar :: Char -> Bool
isAFunChar c = isAlphaNum c || c `elem` "_*+-."

spanAbbrevChar :: String -> (String,String)
spanAbbrevChar          = span isBase64Char

isIntHead :: Char -> Bool
isIntHead c = isDigit c || c == '-'

spanNotQuote' :: String -> (String,String)
spanNotQuote' []                = error "spanNotQuote'"
spanNotQuote' ('"':xs')         = ("\"",xs')
spanNotQuote' ('\\':c:xs')      = case spanNotQuote' xs' of
                                  (ys,zs) -> ('\\':c:ys,zs) 
spanNotQuote' (x:xs')   = case spanNotQuote' xs' of
                               (ys,zs) -> (x:ys,zs) 

condAddRElement :: Int -> Int -> ReadTable -> ReadTable
condAddRElement ai len tbl@(RTab abb_ai_map siz) = 
    if len > 7 || snd (abbrev siz) < len then
       RTab (Map.insert siz ai abb_ai_map) (siz + 1)
    else tbl

condAddWElement :: Int -> Int -> WriteTable -> WriteTable
condAddWElement ai len tbl@(WTab ai_abb_map da@(Doc_len _ doclen) siz) = 
    if len > 7 || doclen < len then
       let nsize = siz + 1 in
       WTab (Map.insert ai da ai_abb_map) (abbrevD nsize) nsize
    else tbl
    -- length $ abbrev (maxBound::Int) == 7, so every ATerm with a
    -- string size greater than 7 must be added

--- From ATerm to String  -----------------------------------------------------

-- a helper data Type for SDocs paired with the associated length
data Doc_len = Doc_len SDoc Int

data Write_struct = WS WriteTable Doc_len

-- an error generated every time when at least one non-empty
-- ATermString is expected!! The Argument should be the throwing
-- function name.
fatal_error :: String -> a 
fatal_error fn = error $ fn ++ ": empty SharedATermString found!!" 

writeATerm :: ATermTable -> String
writeATerm at           = writeAT at ""

writeSharedATermSDoc :: ATermTable -> SDoc
writeSharedATermSDoc at = 
    if getTopIndex at == -1 then fatal_error "writeSharedATermSDoc: empty"
    else case writeTAF (toReadonlyATT at) emptyWTable of
    WS _ (Doc_len doc l)
        | l == 0 -> fatal_error "writeSharedATermSDoc"
        | otherwise -> text "!" <> doc 

writeSharedATerm :: ATermTable -> String 
writeSharedATerm = render . writeSharedATermSDoc

-- non-shared --

writeAT :: ATermTable -> ShowS
writeAT at     =  
    case (getATerm at) of
             (ShAAppl c ts as) -> writeATermAux c (writeAT' at ts) . 
                                  writeParenthesiseAnn (writeAT' at as) 
             (ShAList ts as)   -> bracket (commaSep (writeAT' at ts)) . 
                                  writeParenthesiseAnn (writeAT' at as) 
             (ShAInt i as)     -> showString (show i) . 
                                  writeParenthesiseAnn (writeAT' at as)
-- don't use showInt: can't show negative numbers
writeAT' :: ATermTable -> [Int] -> [ShowS]
writeAT' _at []     = []
writeAT' at (i:is) = let at' = getATermByIndex1 i at 
                         str = writeAT at'
                         strs = writeAT' at is
                     in (str:strs)    
                      
--shared--
writeTAF :: ATermTable -> WriteTable -> Write_struct
writeTAF at tbl@(WTab ai_abb_map _ _) = let i = getTopIndex at in  
    case Map.lookup i ai_abb_map of
    Just s -> WS tbl s 
    Nothing  -> case writeTAF' at tbl of
                (WS tbl' d_len@(Doc_len _ len)) -> 
                    WS (condAddWElement i len tbl') d_len
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
              WS tbl' $ dlConcat (integerDoc i)
                                 (parenthesiseAnnS kidsAnn)

dlConcat :: Doc_len -> Doc_len -> Doc_len               
dlConcat s1@(Doc_len sf1 sl1) s2@(Doc_len sf2 sl2) 
    | sl1 == 0 = s2 
    | sl2 == 0 = s1
    | otherwise = Doc_len (sf1 <> sf2) (sl1 + sl2)

dlConcat_comma :: Doc_len -> Doc_len -> Doc_len         
dlConcat_comma (Doc_len sf1 sl1) (Doc_len sf2 sl2) =
    Doc_len (sf1 <> comma <> sf2) (sl1 + sl2 + 1)

-- produce a String function with a comma seperated string converted ATerms
writeTAFs :: ATermTable -> [Int] -> WriteTable -> Write_struct
writeTAFs at inds tbl = case inds of
    [] -> WS tbl $ Doc_len empty 0
    i : is -> case writeTAF (getATermByIndex1 i at) tbl of
              ws@(WS t1 s1) -> if null is then ws
                else case writeTAFs at is t1 of 
                       WS t2 s2 -> WS t2 $ dlConcat_comma s1 s2

integerDoc :: Integer -> Doc_len
integerDoc i = let s = show i in Doc_len (text s) $ length s

writeATermAux :: String -> [ShowS] -> ShowS
writeATermAux c [] = showString c
writeATermAux c ts = showString c . parenthesise (commaSep ts)

writeATermAuxS :: String -> Doc_len -> Doc_len
writeATermAuxS c doc_len = 
    dlConcat (Doc_len (text c) (length c)) $ parenthesiseS doc_len

writeParenthesiseAnn :: [ShowS] -> ShowS
writeParenthesiseAnn [] = id
writeParenthesiseAnn as = parenthesiseAnn $ commaSep as

commaSep :: [ShowS] -> ShowS
commaSep [] = id
commaSep str = foldr1 (\x y-> x . showChar ',' . y) str

bracket, parenthesise, parenthesiseAnn :: ShowS -> ShowS 
bracket         str = showChar '[' . str . showChar ']'
parenthesise    str = showChar '(' . str . showChar ')'
parenthesiseAnn str = showChar '{' . str . showChar '}'

bracketS, parenthesiseS, parenthesiseAnnS :: Doc_len -> Doc_len
bracketS         (Doc_len d dl) 
    | dl == 0 = Doc_len (text "[]") 2
    | otherwise = Doc_len (brackets d) (dl+2)
parenthesiseS    s@(Doc_len d dl) 
    | dl == 0 = s
    | otherwise = Doc_len (parens d) (dl+2)
parenthesiseAnnS s@(Doc_len d dl) 
    | dl == 0 = s
    | otherwise = Doc_len (braces d) (dl+2)

--- Tables of ATerms ----------------------------------------------------------

-- These Tables consist of FiniteMaps, because all ATerms are indexed
-- with an Int in the second component of the ATermTable. So
-- ATermIndex is the Index that is given by getATermIndex.

-- Map: Abbrev     -> ATermIndex
data ReadTable  = RTab (Map.Map Int Int) Int

-- 1st Map: ATermIndex -> Abbrev
-- TODO: implement 2nd Map as WriteCache 
--         (sf::ShowS,length of String in sf::Int) .. done
data WriteTable = WTab (Map.Map Int Doc_len) Doc_len Int

emptyRTable :: ReadTable
emptyRTable = RTab Map.empty 0

emptyWTable :: WriteTable
emptyWTable = WTab Map.empty (abbrevD 0) 0

getAbbrevTerm :: Int -> ATermTable -> ReadTable -> ShATerm
getAbbrevTerm i at (RTab abb_ai_map _) =  
    getATerm $ getATermByIndex1 (abb_ai_map Map.! i) at 

--- Intger Read ---------------------------------------------------------------

readInteger :: String -> (Integer, Int)
readInteger s = case s of 
                  (hd:str) -> if hd == '-' then case conv str of
                         (m, l) -> (negate m, l + 1)
                         else conv s
                  _ -> error "readInteger"
    where f (m, l) x = (toInteger (ord x - ord '0') + 10 * m, l + 1)
          conv = foldl f (0, 0)

--- Base 64 encoding ----------------------------------------------------------

mkAbbrev :: Int -> (String, Int)
mkAbbrev x
  | x > 0       = mkAbbrevAux x "" 1
  | x == 0      = ("A", 2)
  | otherwise   = error ("mkAbbrev: negative Int "++ show x)

mkAbbrevAux :: Int -> String -> Int -> (String, Int)
mkAbbrevAux x str l = 
  if x > 0 then case quotRem x 64 of 
         (d, m) -> mkAbbrevAux d (toBase64Char m : str) (l + 1)
  else (str, l)

deAbbrev :: [Char] -> Int
deAbbrev =  let f m c = 64 * m + toBase64Int c in foldl f 0 

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
abbrevD i = case abbrev i of (abbStr, len) -> Doc_len (text abbStr) len

abbrev :: Int -> (String, Int)
abbrev i = case mkAbbrev i of (str, l) -> ('#' : str, l)

-- error messages --------------------

error_paren, error_aterm, error_saterm :: String -> String
error_paren s = "Can't parse '" ++ take 1 s ++ 
    "',expecting \",\" or matching parenthesis" ++
    "\nFollowing characters are:" ++ drop 1 s
error_aterm s = "Can't parse '" ++ s ++ 
    "', expecting ATermAppl, ATermList or ATermInt"
error_saterm s = "Can't parse '" ++ s ++ 
    "', expecting Abbreviate, ATermAppl, ATermList or ATermInt"

