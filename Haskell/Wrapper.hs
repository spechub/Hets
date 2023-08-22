{- |
Module      :  ./Haskell/Wrapper.hs
Description :  extract Haskell code in structured specs
Copyright   :  (c) C. Maeder, Uni Bremen 2003
License     :  GPLv2 or higher, see LICENSE.txt

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
import Common.Parsec

hStuff :: CharParser st String
hStuff = flat $ many stuff

stuff :: CharParser st String
stuff = lineComment <|> nestComment <|> stringLit <|> charLit
        <|> balanced "{}"
        <|> balanced "()"
        <|> balanced "[]"
        <|> letter <:> many (alphaNum <|> char '\'')
        <|> single (noneOf "])}") <?> ""

balanced :: String -> CharParser st String
balanced [o, c] = char o <:> hStuff <++> string [c]
balanced _ = error "balanced"

nestComment :: CharParser st String
nestComment = nestedComment "{-" "-}"

lineComment :: CharParser st String
lineComment =
  try ((char '-' <:> many1 (char '-'))
       << notFollowedBy (oneOf "!#$%&*+./<=>?@\\^|~"))
  <++> many (noneOf "\n")

charLit :: CharParser st String
charLit = tryString "'''" <|> sQuoted
