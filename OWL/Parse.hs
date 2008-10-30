{- |
Module      :  $Header$
Description :  Manchester syntax parser for OWL 1.1
Copyright   :  (c) DFKI GmbH, Uni Bremen 2007-2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Manchester syntax parser for OWL 1.1
<http://www.webont.org/owled/2008dc/papers/owled2008dc_paper_11.pdf>
<http://www.faqs.org/rfcs/rfc3987.html>
-}

module OWL.Parse where

import OWL.AS

import Common.Lexer

import Text.ParserCombinators.Parsec
import Data.Char

ncNameStart :: Char -> Bool
ncNameStart c = isAlpha c || c == '_'

ncNameChar :: Char -> Bool
ncNameChar c = isAlphaNum c || elem c ".-_\183"

prefix :: CharParser st String
prefix = satisfy ncNameStart <:> many (satisfy ncNameChar)

iunreserved :: Char -> Bool
iunreserved c = isAlphaNum c || elem c "-._~" || ord c >= 160 && ord c <= 55295

-- maybe lower case hex-digits should be illegal
pctEncoded :: CharParser st String
pctEncoded = char '%' <:> satisfy isHexDigit <:> single (satisfy isHexDigit)

subDelims :: Char -> Bool
subDelims c = elem c "!$&'()*+,;="

iunreservedPctEncodedSubDelims :: String -> CharParser st String
iunreservedPctEncodedSubDelims cs =
    single (satisfy $ \ c -> iunreserved c || subDelims c || elem c cs)
    <|> pctEncoded

ipChar :: CharParser st String
ipChar = iunreservedPctEncodedSubDelims ":@"

ifragment :: CharParser st String
ifragment = flat $ many (ipChar <|> single (char '/' <|> char '?'))

iquery :: CharParser st String
iquery = ifragment -- ignore iprivate

iregName :: CharParser st String
iregName = flat $ many $ iunreservedPctEncodedSubDelims ""

iuserinfo :: CharParser st String
iuserinfo = flat $ many $ iunreservedPctEncodedSubDelims ":"

ihost :: CharParser st String
ihost = iregName -- or ipLiteral or iPv4Adress

port :: CharParser st String
port = many (satisfy isDigit)

iauthority :: CharParser st String
iauthority = option "" (try $ iuserinfo <++> string "@") <++> ihost
    <++> option "" (char ':' <:> port)

isegment :: CharParser st String
isegment = flat $ many ipChar

isegmentNz :: CharParser st String
isegmentNz = flat $ many1 ipChar

isegmentNzNc :: CharParser st String
isegmentNzNc = flat $ many1 $ iunreservedPctEncodedSubDelims "@"

ipathAbempty :: CharParser st String
ipathAbempty = flat $ many (char '/' <:> isegment)

ipathAbsolute :: CharParser st String
ipathAbsolute = char '/' <:> option "" (isegmentNz <++> ipathAbempty)

ipathNoscheme :: CharParser st String
ipathNoscheme = isegmentNzNc <++> ipathAbempty

ipathRootless :: CharParser st String
ipathRootless = isegmentNz <++> ipathAbempty

ipathEmpty :: CharParser st String
ipathEmpty = notFollowedWith (return "") ipChar

iauthorityWithPath :: CharParser st String
iauthorityWithPath = try (string "//") <++> iauthority <++> ipathAbempty

irelativePart :: CharParser st String
irelativePart =
  iauthorityWithPath <|> ipathAbsolute <|> ipathNoscheme <|> ipathEmpty

optQueryOrFrag :: CharParser st String
optQueryOrFrag = option "" (char '?' <:> iquery)
  <++> option "" (char '#' <:> ifragment)

reference :: CharParser st String
reference = irelativePart <++> optQueryOrFrag

curie :: CharParser st String
curie = option "" (try $ prefix <++> string ":") <++> reference

ihierPart :: CharParser st String
ihierPart =
  iauthorityWithPath <|> ipathAbsolute <|> ipathRootless <|> ipathEmpty

scheme :: CharParser st String
scheme = satisfy isAlpha
  <:> many (satisfy $ \ c -> isAlphaNum c || elem c "+-.")

iri :: CharParser st String
iri = scheme <++> string ":" <++> ihierPart <++> optQueryOrFrag

uri :: CharParser st String
uri = try curie <|> iri
