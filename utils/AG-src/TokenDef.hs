{- UU_AG
 - Copyright:  S. Doaitse Swierstra, Arthur I. Baars and Andres Loeh
               Department of Computer Science
               Utrecht University
               P.O. Box 80.089
               3508 TB UTRECHT
               the Netherlands
               {swierstra,arthurb,andres}@cs.uu.nl -}
module TokenDef where

import UU_Parsing
import IOExts

data Token t
  = DATA       {loc :: !Pos}
  | EXT        {loc :: !Pos}
  | ATTR       {loc :: !Pos}
  | SEM        {loc :: !Pos}
  | USE        {loc :: !Pos}
  | LOC        {loc :: !Pos}
  | INCLUDE    {loc :: !Pos}
  | TYPE       {loc :: !Pos}
  | At         {loc :: !Pos}
  | Dot        {loc :: !Pos}
  | Comma      {loc :: !Pos}
  | UScore     {loc :: !Pos}
  | OBrack     {loc :: !Pos}
  | CBrack     {loc :: !Pos}
  | OParens    {loc :: !Pos}
  | CParens    {loc :: !Pos}
  | OBrace     {loc :: !Pos}
  | CBrace     {loc :: !Pos}
  | Colon      {loc :: !Pos}
  | Equals     {loc :: !Pos}
  | ColonEquals{loc :: !Pos}
  | Bar        {loc :: !Pos}
  | Varid      {varid::String, loc :: !Pos}
  | Conid      {conid::String, loc :: !Pos}
  | StrLit     {string::String, loc :: !Pos}
  | Codescrap  {code::[t],     loc :: !Pos}
  | TkError    {msg::String,   loc :: !Pos}

data Pos = Pos{file:: String,line:: !Int,column:: !Int}

-- deleteCost; insertCost ????
instance Symbol (Token Char)  where
 deleteCost (TkError   _  _) = 0
 deleteCost (DATA         _) = 7
 deleteCost (EXT          _) = 7
 deleteCost (ATTR         _) = 7
 deleteCost (SEM          _) = 7
 deleteCost (USE          _) = 7
 deleteCost (INCLUDE      _) = 7
 deleteCost _                = 5



instance Ord    (Token a) where
  compare x y = getIndex x `compare` getIndex y

getIndex :: Token t -> Int
getIndex (Varid     _  _) = 0
getIndex (Conid     _  _) = 1
getIndex (Codescrap _  _) = 2
getIndex (TkError   _  _) = 3
getIndex (DATA         _) = 4
getIndex (EXT          _) = 5
getIndex (ATTR         _) = 6
getIndex (SEM          _) = 7
getIndex (USE          _) = 8
getIndex (LOC          _) = 10
getIndex (INCLUDE      _) = 11
getIndex (TYPE         _) = 12
getIndex (At           _) = 13
getIndex (Dot          _) = 14
getIndex (Comma        _) = 15
getIndex (UScore       _) = 16
getIndex (OBrack       _) = 17
getIndex (CBrack       _) = 18
getIndex (OParens      _) = 19
getIndex (CParens      _) = 20
getIndex (OBrace       _) = 21
getIndex (CBrace       _) = 22
getIndex (Colon        _) = 23
getIndex (Equals       _) = 24
getIndex (ColonEquals  _) = 25
getIndex (Bar          _) = 26
getIndex (StrLit   _   _) = 27

instance Eq     (Token a) where
 x == y = getIndex x == getIndex y

keyword w  = "keyword " ++ show w
symbol s   = "symbol "  ++ show s

instance Show a => Show   (Token a) where
  show (Varid     v  p) = "lowercase identifier " ++ show v
  show (Conid     c  p) = "uppercase identifier " ++ show c
  show (StrLit    s  p) = "literal string " ++ show s
  show (Codescrap c  p) = "code scrap:{" ++ show c ++ "}"
  show (TkError   m  p) = m ++ show p
  show (DATA        p) = keyword "DATA"
  show (EXT         p) = keyword "EXT"
  show (ATTR        p) = keyword "ATTR"
  show (SEM         p) = keyword "SEM"
  show (USE         p) = keyword "USE"
  show (LOC         p) = keyword "loc"
  show (INCLUDE     p) = keyword "INCLUDE"
  show (TYPE        p) = keyword "TYPE"
  show (At          p) = symbol "@"
  show (Dot         p) = symbol "."
  show (Comma       p) = symbol ","
  show (UScore      p) = symbol "_"
  show (OBrack      p) = symbol "["
  show (CBrack      p) = symbol "]"
  show (OParens     p) = symbol "("
  show (CParens     p) = symbol ")"
  show (OBrace      p) = symbol "{"
  show (CBrace      p) = symbol "}"
  show (Colon       p) = symbol ":"
  show (Equals      p) = symbol "="
  show (ColonEquals p) = symbol ":="
  show (Bar         p) = symbol "|"

instance Show Pos where
  show p | line p == (-1) = ""
         | otherwise      = (file p) ++ ":" ++ show(line p) ++ "." ++ show(column p) ++","

updPos :: Char -> Pos -> Pos
updPos c p = case c of
  '\t' -> tab p
  '\n' -> newl p
  _    -> advc 1 p

updPos' :: Char -> Pos -> (Pos -> a) -> a
updPos' c p cont = p `seq` cont (updPos c p)

advc' :: Int -> Pos -> (Pos -> b) -> b
advc' i p cont = p `seq` cont (advc i p)

tab' :: Pos -> (Pos -> a) -> a
tab'  p cont = p `seq` cont (tab p)

newl' :: Pos -> (Pos -> a) -> a
newl' p cont = p `seq` cont (newl p)

advc :: Int -> Pos -> Pos
advc i p = p{column=column p + i}

tab :: Pos -> Pos
tab p = p{column=old + 8 - ((old-1) `mod` 8)}
   where old = column p

newl :: Pos -> Pos
newl p = p{line=line p + 1, column=1}

initPos :: FilePath -> Pos
initPos f = Pos{file=f,line=1,column=1}

noPos :: Pos
noPos = Pos{file="",line=(-1),column=(-1)}
