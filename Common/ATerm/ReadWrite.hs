{- |
Module      :  $Header$
Description :  read and write ATerms to and from strings
Copyright   :  (c) Klaus Luettich, C.Maeder, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports ATerm.AbstractSyntax)

convert 'ShATerm's in 'ATermTable's to and from base64 encoded 'String's
  and 'SDoc's shared (TAF format) and unshared
-}

module Common.ATerm.ReadWrite
    ( readATerm
    , writeATerm
    , writeATermSDoc
    , writeSharedATerm
    , writeSharedATermSDoc
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

        accidental support for the empty aterm: ShAAppl "" [] []
-}

import Common.ATerm.AbstractSyntax
import Common.SimpPretty
import Common.Base64
import Data.Char
import qualified Data.IntMap as IntMap

--- From String to ATerm ------------------------------------------------------

data ReadTAFStruct = RTS
    ATermTable
    String -- remaing string
    (AbbrevTable Int)
    Int -- string length of last ATerm read

readATerm :: String -> ATermTable
readATerm = readATerm' . dropWhile ( \ c -> case c of
    '!' -> True
    _ -> isSpace c)

readATerm' :: String -> ATermTable
readATerm' str =
    case readTAF emptyATermTable str emptyATab of
    (RTS at rt _ _, _) -> case dropSpaces rt of
       [] -> toReadonlyATT at
       s -> error $ "garbage following aterm: " ++ take 10 s

-- non-shared is a special case of shared (but could be made more fool proof)

readTAF :: ATermTable -> String -> AbbrevTable Int -> (ReadTAFStruct, Int)
readTAF at str tbl = case readTAF' at str tbl of
    (rs@(RTS at' str' tbl' l'), eith) -> case eith of
        Left i -> (rs, i)
        Right a -> case addATerm a at' of
            (at'', i) ->
                (RTS at'' str' (insertATab l' (sizeATab tbl') i tbl') l', i)

readTAF' :: ATermTable -> String -> AbbrevTable Int
         -> (ReadTAFStruct, Either Int ShATerm)
readTAF' at str tbl = case str of
  '#' : xs -> case spanAbbrevChar xs of
      (i, str') -> case lookupATab (deAbbrev i) tbl of
          Nothing -> error $ "unknown aterm index " ++ '#' : i
          Just a -> (RTS at str' tbl $ length i + 1, Left a)
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

readParenTAFs :: ATermTable -> String -> AbbrevTable Int -> Int
              -> (ReadTAFStruct, [Int])
readParenTAFs = readParTAFs '(' ')'

readParTAFs :: Char -> Char -> ATermTable -> String -> AbbrevTable Int -> Int
              -> (ReadTAFStruct, [Int])
readParTAFs op cp at str tbl l = case str of
    p : r | op == p -> readTAFs0 at cp (dropSpaces r) tbl $ l + 1
    _ -> (RTS at str tbl l, [])

readTAFs0 :: ATermTable -> Char -> String -> AbbrevTable Int -> Int
         -> (ReadTAFStruct, [Int])
readTAFs0 at par str tbl l = case str of
    p : r | par == p -> (RTS at r tbl $ l + 1, [])
    _ -> readTAFs1 at par str tbl l

readTAFs1 :: ATermTable -> Char -> String -> AbbrevTable Int -> Int
          -> (ReadTAFStruct, [Int])
readTAFs1 at par str tbl l =
    case readTAF at (dropSpaces str) tbl of
      (RTS at' str'  tbl'  l', t) ->
          case readTAFs2 at' par (dropSpaces str') tbl' $ l + l' of
            (RTS at'' str'' tbl'' l'', ts) ->
                (RTS at'' str'' tbl'' l'', t : ts)

readTAFs2 :: ATermTable -> Char -> String -> AbbrevTable Int -> Int
          -> (ReadTAFStruct, [Int])
readTAFs2 at par str tbl l = case str of
    ',' : r -> readTAFs1 at par (dropSpaces r) tbl $ l + 1
    p : r | par == p -> (RTS at r tbl $ l + 1, [])
    _ -> error $ "expecting ',' or '" ++ [par] ++ "' in aterm but found: "
         ++ take 10 str

readAnnTAF :: ATermTable -> String -> AbbrevTable Int -> Int
           -> (ReadTAFStruct, [Int])
readAnnTAF = readParTAFs '{' '}'

-- helpers --

dropSpaces :: String -> String
dropSpaces = dropWhile isSpace

readAFun :: String -> (String, String)
readAFun str = case str of
  q : r | q == '"' -> let (c, s) = spanNotQuote' r in (q : c, s)
  _ -> span isAFunChar str

spanNotQuote' :: String -> (String, String)
spanNotQuote' str = case str of
     q : r | q == '"'  -> ([q], r)
     c : r@(d : s) -> let
         (e, l) = if c == '\\' then ([c, d], s) else ([c], r)
         (f, t) = spanNotQuote' l
         in (e ++ f, t)
     _ -> error $ "wrongly terminated aterm string: " ++ take 10 str

isAFunChar :: Char -> Bool
isAFunChar c = isAlphaNum c || c `elem` "_*+-."

spanAbbrevChar :: String -> (String, String)
spanAbbrevChar = span isBase64Char

isIntHead :: Char -> Bool
isIntHead c = isDigit c || c == '-'

--- From (shared) ATerms to strings via simple documents with associated length

data Doc_len = Doc_len SDoc Int

data Write_struct = WS (AbbrevTable Doc_len) Doc_len

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
    case writeTAF b (toReadonlyATT at) emptyATab of
    WS _ (Doc_len doc _) -> (if b then text "!" else empty) <> doc

--shared (if input is True)

writeTAF :: Bool -> ATermTable -> AbbrevTable Doc_len -> Write_struct
writeTAF b at tbl = let i = getTopIndex at in
    case lookupATab i tbl of
    Just s -> if b then WS tbl s else writeTAF' b at tbl
    Nothing  -> case writeTAF' b at tbl of
        WS tbl' d_len@(Doc_len _ len) ->
            WS (insertATab len i (abbrevD $ sizeATab tbl') tbl') d_len

writeTAF' :: Bool -> ATermTable -> AbbrevTable Doc_len -> Write_struct
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

-- produce comma seperated output from aterm indices
writeTAFs :: Bool -> ATermTable -> [Int] -> AbbrevTable Doc_len -> Write_struct
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

-- list brackets must not be omitted
bracketS :: Doc_len -> Doc_len
bracketS         (Doc_len d dl)
    | dl == 0 = doc_len "[]"
    | otherwise = Doc_len (brackets d) $ dl + 2

parenthesiseS :: Doc_len -> Doc_len
parenthesiseS    s@(Doc_len d dl)
    | dl == 0 = s
    | otherwise = Doc_len (parens d) $ dl + 2

parenthesiseAnnS :: Doc_len -> Doc_len
parenthesiseAnnS s@(Doc_len d dl)
    | dl == 0 = s
    | otherwise = Doc_len (braces d) $ dl + 2

{- | This abbreviation table maps abbreviation ints to aterm indices for
     reading and aterm indices to abbreviation docs during writing. -}
data AbbrevTable a = ATab !(IntMap.IntMap a) !(Int, Int) !Int

{- The last component is the current maximal abbreviation int that
serves as a key when reading and as a value when writing. The pair
stores the size of this component and the maximal power of 64
that is less than it, in order to simplify the computation of the size
of the next abbreviation int. -}

-- | initial table
emptyATab :: AbbrevTable a
emptyATab = ATab IntMap.empty (2, 64) 0

-- | only insert if the first argument is greater than the abbreviation size
insertATab :: Int -> Int -> a -> AbbrevTable a -> AbbrevTable a
insertATab dl i a t@(ATab m p@(sl, b) s) =
    if dl > sl then let n = s + 1 in
        ATab (IntMap.insert i a m)
           (if rem n b == 0 then (sl + 1, 64 * b) else p) n
    else t

-- | get current abbreviation size
sizeATab :: AbbrevTable a -> Int
sizeATab (ATab _ _ s) = s

-- | lookup map value
lookupATab :: Int -> AbbrevTable a -> Maybe a
lookupATab i (ATab m _ _) = IntMap.lookup i m

--- Intger Read ---------------------------------------------------------------

readInteger :: String -> (Integer, Int)
readInteger s = case s of
                  (hd:str) -> if hd == '-' then case conv str of
                         (m, l) -> (negate m, l + 1)
                         else conv s
                  _ -> error "readInteger"
    where f (m, l) x = (toInteger (ord x - ord0) + 10 * m, l + 1)
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
