{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, C.Maeder, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

-}

module Common.ATerm.ReadWrite (

        readATerm,       -- :: String -> ATermTable
        writeATerm,      -- :: ATermTable -> String
        writeATermSDoc,  -- :: ATermTable -> SDoc
        writeSharedATerm,-- :: ATermTable -> String
        writeSharedATermSDoc -- :: ATermTable -> SDoc
) where

{-
        Author: Joost Visser, CWI, 2002
        Changed by: Klaus Luettich & Felix Reckers, 2002-2003, C. Maeder 2005

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
readATerm = readATerm' . dropWhile ( \ c -> isSpace c || c == '!')

readATerm' :: String -> ATermTable
readATerm' str =
    case readTAF emptyATermTable str emptyRTable of
    (RTS at rt _ _, _) -> case dropSpaces rt of 
       [] -> toReadonlyATT at
       s -> error $ "garbage following aterm: " ++ take 10 s 

-- non-shared is a special case of shared

readTAF :: ATermTable -> String -> ReadTable -> (ReadTAFStruct, Int)
readTAF at str tbl = case readTAF' at str tbl of
    (rs@(RTS at' str' tbl' l'), eith) -> case eith of
        Left i -> (rs, i)
        Right a -> case addATerm a at' of
            (at'', i) ->
                (RTS at'' str' (condAddRElement i l' tbl') l', i)

readTAF' :: ATermTable -> String -> ReadTable 
         -> (ReadTAFStruct, Either Int ShATerm)
readTAF' at str tbl = case str of
  '#' : xs -> case spanAbbrevChar xs of
      (i, str') -> (RTS at str' tbl $ length i + 1, 
                    Left $ getAbbrevTerm (deAbbrev i) tbl)
  '[' : _ -> case readParTAFs '[' ']' at str tbl 0 of
      (RTS at' str'  tbl'  l', kids) ->
          case readAnnTAF at' (dropSpaces str') tbl' l' of
            (rs, ann) -> (rs, Right $ ShAList kids ann)
  x : xs | isIntHead x -> case span isDigit xs of
      (i, str') -> let (intl, l') = readInteger $ x : i in
          case readAnnTAF at (dropSpaces str') tbl l' of
            (rs, ann) -> (rs, Right $ ShAInt intl ann)
  _ -> case readAFun str of
      (c, str') -> case readParenTAFs at (dropSpaces str') tbl $ length c of
          (RTS at' str'' tbl' l', kids) ->
              case readAnnTAF at' (dropSpaces str'') tbl' l' of
                (rs, ann) -> (rs, Right $ ShAAppl c kids ann)

readParenTAFs :: ATermTable -> String -> ReadTable -> Int
              -> (ReadTAFStruct, [Int])
readParenTAFs = readParTAFs '(' ')'

readParTAFs :: Char -> Char -> ATermTable -> String -> ReadTable -> Int
              -> (ReadTAFStruct, [Int])
readParTAFs op cp at str tbl l = case str of
    p : r | op == p -> readTAFs0 at cp (dropSpaces r) tbl $ l + 1
    _ -> (RTS at str tbl l, [])

readTAFs0 :: ATermTable -> Char -> String -> ReadTable -> Int
         -> (ReadTAFStruct, [Int])
readTAFs0 at par str tbl l = case str of 
    p : r | par == p -> (RTS at r tbl $ l + 1, [])
    _ -> readTAFs1 at par str tbl l 

readTAFs1 :: ATermTable -> Char -> String -> ReadTable -> Int
          -> (ReadTAFStruct, [Int])
readTAFs1 at par str tbl l =
    case readTAF at (dropSpaces str) tbl of
      (RTS at' str'  tbl'  l', t) ->
          case readTAFs2 at' par (dropSpaces str') tbl' $ l + l' of
            (RTS at'' str'' tbl'' l'', ts) -> 
                (RTS at'' str'' tbl'' l'', t : ts)

readTAFs2 :: ATermTable -> Char -> String -> ReadTable -> Int
          -> (ReadTAFStruct, [Int])
readTAFs2 at par str tbl l = case str of 
    ',' : r -> readTAFs1 at par (dropSpaces r) tbl $ l + 1
    p : r | par == p -> (RTS at r tbl $ l + 1, [])
    _ -> error $ "expecting ',' or '" ++ [par] ++ "' in aterm but found: " 
         ++ take 10 str

readAnnTAF :: ATermTable -> String -> ReadTable -> Int -> (ReadTAFStruct, [Int])
readAnnTAF = readParTAFs '{' '}'

-- helpers --

dropSpaces :: String -> String
dropSpaces = dropWhile isSpace

readAFun :: String -> (String,String)
readAFun str = case str of 
  q : r | q == '"' -> let (c, s) = spanNotQuote' r in (q : c, s)
  _ -> span isAFunChar str

spanNotQuote' :: String -> (String,String)
spanNotQuote' str = case str of
     q : r | q == '"'  -> ([q], r)
     c : r@(d : s) -> let 
         (e, l) = if c == '\\' then ([c, d], s) else ([c], r)
         (f, t) = spanNotQuote' l
         in (e ++ f, t)
     _ -> error $ "wrongly terminated aterm string: " ++ take 10 str

isAFunChar :: Char -> Bool
isAFunChar c = isAlphaNum c || c `elem` "_*+-."

spanAbbrevChar :: String -> (String,String)
spanAbbrevChar = span isBase64Char

isIntHead :: Char -> Bool
isIntHead c = isDigit c || c == '-'

condAddRElement :: Int -> Int -> ReadTable -> ReadTable
condAddRElement ai len tbl@(RTab abb_ai_map p@(sizL, modV) siz) =
    if sizL < len then
       let s = siz + 1 in RTab (Map.insert siz ai abb_ai_map) 
           (if rem s modV == 0 then (sizL + 1, 64 * modV) else p) s
    else tbl

condAddWElement :: Int -> Int -> WriteTable -> WriteTable
condAddWElement ai len tbl@(WTab ai_abb_map siz) =
    case abbrevD siz of 
      da@(Doc_len _ docLen) -> if docLen < len 
          then WTab (Map.insert ai da ai_abb_map) $ siz + 1
          else tbl

--- From ATerm to String  -----------------------------------------------------

-- a helper data Type for SDocs paired with the associated length
data Doc_len = Doc_len SDoc Int

data Write_struct = WS WriteTable Doc_len

writeATerm :: ATermTable -> String
writeATerm = render . writeATermSDoc

writeATermSDoc :: ATermTable -> SDoc
writeATermSDoc = writeSharedATermSDoc' False

writeSharedATermSDoc :: ATermTable -> SDoc
writeSharedATermSDoc = writeSharedATermSDoc' True

writeSharedATerm :: ATermTable -> String
writeSharedATerm = render . writeSharedATermSDoc

writeSharedATermSDoc' :: Bool -> ATermTable -> SDoc
writeSharedATermSDoc' b at =
    case writeTAF b (toReadonlyATT at) emptyWTable of
    WS _ (Doc_len doc _) -> (if b then text "!" else empty) <> doc

--shared (if input is True)

writeTAF :: Bool -> ATermTable -> WriteTable -> Write_struct
writeTAF b at tbl@(WTab ai_abb_map _) = let i = getTopIndex at in
    case Map.lookup i ai_abb_map of
    Just s -> if b then WS tbl s else writeTAF' b at tbl
    Nothing  -> case writeTAF' b at tbl of
        WS tbl' d_len@(Doc_len _ len) -> WS (condAddWElement i len tbl') d_len

writeTAF' :: Bool -> ATermTable -> WriteTable -> Write_struct
writeTAF' b at tbl = case getATerm at of
    ShAAppl c ts anns -> case writeTAFs b at ts tbl of
        WS tbl' kids -> case writeTAFs b at anns tbl' of
            WS tbl'' kidsAnn -> WS tbl'' $ dlConcat (writeATermAuxS c kids)
                                $ parenthesiseAnnS kidsAnn
    ShAList ts anns -> case writeTAFs b at ts tbl of
        WS tbl' kids -> case writeTAFs b at anns tbl' of
            WS tbl'' kidsAnn -> WS tbl'' $ dlConcat (bracketS kids)
                                $ parenthesiseAnnS kidsAnn
    ShAInt i anns -> case writeTAFs b at anns tbl of
        WS tbl' kidsAnn -> WS tbl' $ dlConcat (integerDoc i)
                           $ parenthesiseAnnS kidsAnn

dlConcat :: Doc_len -> Doc_len -> Doc_len
dlConcat s1@(Doc_len sf1 sl1) s2@(Doc_len sf2 sl2)
    | sl1 == 0 = s2
    | sl2 == 0 = s1
    | otherwise = Doc_len (sf1 <> sf2) $ sl1 + sl2 

dlConcat_comma :: Doc_len -> Doc_len -> Doc_len
dlConcat_comma (Doc_len sf1 sl1) (Doc_len sf2 sl2) =
    Doc_len (sf1 <> comma <> sf2) $ sl1 + sl2 + 1

-- produce a String function with a comma seperated string converted ATerms
writeTAFs :: Bool -> ATermTable -> [Int] -> WriteTable -> Write_struct
writeTAFs b at inds tbl = case inds of
    [] -> WS tbl $ Doc_len empty 0
    i : is -> case writeTAF b (getATermByIndex1 i at) tbl of
              ws@(WS t1 s1) -> if null is then ws
                else case writeTAFs b at is t1 of
                       WS t2 s2 -> WS t2 $ dlConcat_comma s1 s2

doc_len :: String -> Doc_len
doc_len s = Doc_len (text s) $ length s

integerDoc :: Integer -> Doc_len
integerDoc = doc_len . show

writeATermAuxS :: String -> Doc_len -> Doc_len
writeATermAuxS s = dlConcat (doc_len s) . parenthesiseS

bracketS, parenthesiseS, parenthesiseAnnS :: Doc_len -> Doc_len
bracketS         (Doc_len d dl)
    | dl == 0 = doc_len "[]"
    | otherwise = Doc_len (brackets d) $ dl + 2
parenthesiseS    s@(Doc_len d dl)
    | dl == 0 = s
    | otherwise = Doc_len (parens d) $ dl + 2
parenthesiseAnnS s@(Doc_len d dl)
    | dl == 0 = s
    | otherwise = Doc_len (braces d) $ dl + 2

--- Tables of ATerms ----------------------------------------------------------

-- These Tables consist of FiniteMaps, because all ATerms are indexed
-- with an Int in the second component of the ATermTable. So
-- ATermIndex is the Index that is given by getATermIndex.

-- Map: Abbrev     -> ATermIndex
data ReadTable  = RTab (Map.Map Int Int) (Int, Int) Int 
       -- (length of size, 64^i) and size

data WriteTable = WTab (Map.Map Int Doc_len) Int

emptyRTable :: ReadTable
emptyRTable = RTab Map.empty (2, 64) 0

emptyWTable :: WriteTable
emptyWTable = WTab Map.empty 0

getAbbrevTerm :: Int -> ReadTable -> Int
getAbbrevTerm i (RTab abb_ai_map _ _) = case Map.lookup i abb_ai_map of 
    Nothing -> error $ "unknown aterm index " ++ abbrev i
    Just a -> a

--- Intger Read ---------------------------------------------------------------

readInteger :: String -> (Integer, Int)
readInteger s = case s of
                  (hd:str) -> if hd == '-' then case conv str of
                         (m, l) -> (negate m, l + 1)
                         else conv s
                  _ -> error "readInteger"
    where f (m, l) x = (toInteger (digitToInt x) + 10 * m, l + 1)
          conv = foldl f (0, 0)

--- Base 64 encoding ----------------------------------------------------------

abbrevD :: Int -> Doc_len
abbrevD i = doc_len $ abbrev i

abbrev :: Int -> String
abbrev i = '#' : mkAbbrev i

mkAbbrev :: Int -> String
mkAbbrev x = if x > 0 then mkAbbrevAux x "" else "A" 

mkAbbrevAux :: Int -> String -> String
mkAbbrevAux x str =
  if x > 0 then case quotRem x 64 of
         (d, m) -> mkAbbrevAux d $ toBase64Char m : str
  else str

deAbbrev :: [Char] -> Int
deAbbrev = let f m c = 64 * m + toBase64Int c in foldl f 0

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
    | isUpper c = ord c - ordA
    | isLower c = ord c - orda_26
    | isDigit c = ord c + mord0_52
    | c == '+' = 62
    | otherwise = 63 -- '/'

ordA :: Int
ordA = ord 'A'

orda_26 :: Int
orda_26 = ord 'a' - 26

mord0_52 :: Int
mord0_52 = 52 - ord '0'

toBase64Char :: Int -> Char
toBase64Char i
    | i < 26 = chr (ordA + i)
    | i < 52 = chr (orda_26 + i)
    | i < 62 = chr (i - mord0_52)
    | i == 62 = '+'
    | otherwise = '/' -- 63

isBase64Char :: Char -> Bool
isBase64Char c = isAscii c && (isAlphaNum c || c == '+' || c == '/')
