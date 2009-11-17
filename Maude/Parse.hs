{- |
Module      :  $Header$
Description :  extract Maude text in structured specs
Copyright   :  (c) C. Maeder, DFKI GmbH 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

extract Maude text from structured specs and stops at an unbalanced curly brace
-}

module Maude.Parse where

import Text.ParserCombinators.Parsec
import Common.Lexer

mStuff :: CharParser st String
mStuff = flat . many $ lineComment <|> blockComment <|> stringLit
        <|> balanced "{}"
        <|> balanced "()"
        <|> balanced "[]"
        <|> (char '`' <:> single anyChar)
        <|> fmap (: []) (noneOf "\"`])}")

balanced :: String -> CharParser st String
balanced [o, c] = char o <:> mStuff <++> string [c]
balanced _ = error "balanced"

blockComment :: CharParser st String
blockComment = try (string "***(") <++>
   parbalanced <++> string ")"

parbalanced :: CharParser st String
parbalanced = flat . many $ char '(' <:> parbalanced <++> string ")"
  <|> many1 (noneOf "()")

lineComment :: CharParser st String
lineComment = (try (string "---") <|> try (string "***"))
              <++> many (noneOf "\n\r")
              <++> many (oneOf "\n\r")

stringLit :: CharParser st String
stringLit = enclosedBy (flat $ many $ single (noneOf "\\\"")
                        <|> char '\\' <:> single anyChar) $ char '\"'
