{- |
Module      :  $Header$
Copyright   :  (c) C. Maeder and Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

parse the outer syntax of an Isabelle theory file
-}

module Isabelle.IsaParse where

import Common.Lexer
import Text.ParserCombinators.Parsec

latin :: CharParser st String
latin = single letter <?> "latin"

greek :: CharParser st String
greek = string "\\<" <++> 
         option "" (string "^") -- isup or isup
         <++> many1 letter <++> string ">" <?> "greek"

isaLetter :: CharParser st String
isaLetter = latin <|> greek

quasiletter :: CharParser st String
quasiletter = single (digit <|> prime <|> char '_' ) <|> isaLetter
              <?> "quasiletter"

ident :: CharParser st String
ident = isaLetter <++> flat (many quasiletter)

longident :: CharParser st String
longident = ident <++> flat (many $ char '.' <:> ident)

symident :: CharParser st String
symident = many1 (oneOf "!#$&*+-/:<=>?@^_|~" <?> "sym") <|> greek

isaString :: CharParser st String
isaString = enclosedBy (flat $ many (single (noneOf "\\\"")
                                 <|> char '\\' <:> single anyChar))
            (char '\"')

verbatim :: CharParser st String
verbatim = plainBlock "{*" "*}"

nestComment :: CharParser st String
nestComment = nestedComment "(*" "*)"

nat :: CharParser st String
nat = many1 digit <?> "nat"

name :: CharParser st String
name = ident <|> symident <|> isaString <|> nat

nameref :: CharParser st String
nameref = longident <|> symident <|> isaString <|> nat

text :: CharParser st String 
text = nameref <|> verbatim

isaSkip :: CharParser st ()
isaSkip = skipMany (many1 space <|> nestComment <?> "")

comment :: CharParser st String 
comment = try (string "--") >> isaSkip >> text


