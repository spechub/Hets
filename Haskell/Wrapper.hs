{- |
Module:  $Header$
Copyright   :  (c) C. Maeder, Uni Bremen 2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

extract Haskell code from String
-}

{-
   stops at unbalanced "}"

   "then" may be recognized if it is not preceded by "if"
   but that's not worth the trouble, because ...

   "and" is used by Haskell,
   "with", "hide", "reveal", "within", "end"
   may be userdefined in Haskell
-}

module Haskell.Wrapper where

import Text.ParserCombinators.Parsec
import Common.Lexer
import Data.Char

hStuff, stuff :: CharParser st String
hStuff = flat $ many stuff

stuff = lineComment <|> nestComment <|> stringLit <|> charLit
        <|> balanced "{}"
        <|> balanced "()"
        <|> balanced "[]"
        <|> satisfy isAlpha <:> many (satisfy isAlphaNum <|> prime)
        <|> single (noneOf "])}") <?> ""

balanced :: String -> CharParser st String
balanced [o, c] = char o <:> hStuff <++> string [c]
balanced _ = error "balanced"

nestComment :: CharParser st String
nestComment = nestedComment "{-" "-}"

lineComment, stringLit, charLit :: CharParser st String
lineComment = try (string "--") <++> many (noneOf "\n\r")
              <++> many (oneOf "\n\r")

stringLit = enclosedBy (flat $ many $ single (noneOf "\\\"")
                        <|> char '\\' <:> single anyChar) $ char '\"'

charLit = try (string "'''") <|>
          enclosedBy (flat $ many $ single (noneOf "\\\'")
                      <|> char '\\' <:> single anyChar)
          (char '\'')
