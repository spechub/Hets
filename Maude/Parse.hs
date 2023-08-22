{- |
Module      :  ./Maude/Parse.hs
Description :  extract Maude text in structured specs
Copyright   :  (c) C. Maeder, DFKI GmbH 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

extract Maude text from structured specs and stops at an unbalanced curly brace
-}

module Maude.Parse where

import Text.ParserCombinators.Parsec
import Common.Parsec

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
blockComment = tryString "***(" <++> parbalanced <++> string ")"

parbalanced :: CharParser st String
parbalanced = flat . many $ char '(' <:> parbalanced <++> string ")"
  <|> many1 (noneOf "()")

lineComment :: CharParser st String
lineComment = (tryString "---" <|> tryString "***")
              <++> many (noneOf "\n")
