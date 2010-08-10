-- parser for derive commands
module CommandP (local, command, header, cap, imports) where

import ParseLib2
import DataP

-- command syntax
{-! global : rule1, rule2, rule !-}
{-! derive : rule1, rule2, !-}
{-! for ty derive : rule , rule 2, .. !-}

command :: Parser ([String], Data)
command = annotation global +++ annotation forType

local :: Parser [String]
local = annotation loc

global :: Parser ([String], Data)
global = do
  symbol "global"
  symbol ":"
  ts <- tag `sepby` symbol ","
  return (ts, Directive)

forType :: Parser ([String], Data)
forType = do
  symbol "for"
  ty <- cap
  symbol "derive"
  symbol ":"
  ts <- tag `sepby` symbol ","
  return (ts, TypeName ty)

loc :: Parser [String]
loc = do
  symbol "derive"
  symbol ":"
  tag `sepby` symbol ","

cap :: Parser String
cap = token $ do
  x <- upper
  xs <- many alphanum
  return (x : xs)

tag :: Parser String
tag = token (many alphanum)

annotation :: Parser b -> Parser b
annotation x = do
  symbol "{-!"
  r <- x
  symbol "!-}"
  return r

-- parser for module headers

header :: Parser [String]
header = do
  symbol "module"
  cap
  opt (skipNest (symbol "(") (symbol ")") >> return [])
  symbol "where"
  many imports

imports :: Parser String
imports = do
  symbol "import"
  opt (symbol "qualified")
  i <- cap
  opt (symbol "as" >> cap)
  opt (symbol "hiding")
  opt (skipNest (symbol "(") (symbol ")") >> return [])
  return i
