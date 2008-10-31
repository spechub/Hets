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
<http://www.faqs.org/rfcs/rfc4646.html>
-}

module OWL.Parse where

import OWL.AS

import Common.Lexer

import Text.ParserCombinators.Parsec
import Data.Char

ncNameStart :: Char -> Bool
ncNameStart c = isAlpha c || c == '_'

-- | rfc3987 plus '+' from scheme (scheme does not allow the dots)
ncNameChar :: Char -> Bool
ncNameChar c = isAlphaNum c || elem c ".+-_\183"

prefix :: CharParser st String
prefix = satisfy ncNameStart <:> many (satisfy ncNameChar)

iunreserved :: Char -> Bool
iunreserved c = isAlphaNum c || elem c "-._~" || ord c >= 160 && ord c <= 55295

-- maybe lower case hex-digits should be illegal
pctEncoded :: CharParser st String
pctEncoded = char '%' <:> hexDigit <:> single hexDigit

subDelims :: Char -> Bool
subDelims c = elem c "!$&'()*+,;="

iunreservedSubDelims :: String -> CharParser st Char
iunreservedSubDelims cs =
    satisfy $ \ c -> iunreserved c || subDelims c || elem c cs

iunreservedPctEncodedSubDelims :: String -> CharParser st String
iunreservedPctEncodedSubDelims cs =
    single (iunreservedSubDelims cs) <|> pctEncoded

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

-- | parse zero or at most n consecutive arguments
atMost :: Int -> GenParser tok st a -> GenParser tok st [a]
atMost n p = if n <= 0 then return [] else
     p <:> atMost (n - 1) p <|> return []

-- | parse at least one but at most n conse
atMost1 :: Int -> GenParser tok st a -> GenParser tok st [a]
atMost1 n p = p <:> atMost (n - 1) p

decOctet :: CharParser st String
decOctet = atMost 3 digit
  `checkWith` \ s -> let v = value 10 s in v <= 255 &&
                             (if v == 0 then s == "0" else take 1 s /= "0")

iPv4Adress :: CharParser st String
iPv4Adress = decOctet <++> string "."
  <++> decOctet <++> string "."
  <++> decOctet <++> string "."
  <++> decOctet

ihost :: CharParser st String
ihost = iregName <|> iPv4Adress -- or ipLiteral

port :: CharParser st String
port = many digit

iauthority :: CharParser st String
iauthority = option "" (try $ iuserinfo <++> string "@") <++> ihost
    <++> option "" (char ':' <:> port)

isegment :: CharParser st String
isegment = flat $ many ipChar

isegmentNz :: CharParser st String
isegmentNz = flat $ many1 ipChar

ipathAbempty :: CharParser st String
ipathAbempty = flat $ many (char '/' <:> isegment)

ipathAbsolute :: CharParser st String
ipathAbsolute = char '/' <:> option "" (isegmentNz <++> ipathAbempty)

ipathRootless :: CharParser st String
ipathRootless = isegmentNz <++> ipathAbempty

ipathEmpty :: CharParser st String
ipathEmpty = notFollowedBy (iunreservedSubDelims ":@% ") >> return ""

iauthorityWithPath :: CharParser st String
iauthorityWithPath = try (string "//") <++> iauthority <++> ipathAbempty

optQueryOrFrag :: CharParser st String
optQueryOrFrag = option "" (char '?' <:> iquery)
  <++> option "" (char '#' <:> ifragment)

-- | covers irelative-part (therefore we omit curie)
ihierPart :: CharParser st String
ihierPart =
  iauthorityWithPath <|> ipathAbsolute <|> ipathRootless <|> ipathEmpty

hierPartWithOpts :: CharParser st String
hierPartWithOpts = ihierPart <++> optQueryOrFrag

uriP :: CharParser st QName
uriP =  do
    pre <- try (prefix << char ':')
    r <- hierPartWithOpts
    return $ QN pre r ""
  <|> fmap mkQName hierPartWithOpts

datatype :: CharParser st QName
datatype = fmap mkQName
  (choice $ map (try . string) ["integer", "decimal", "float", "string"])
  <|> uriP

stringLit :: CharParser st String
stringLit = enclosedBy (flat $ many $ single (noneOf "\\\"")
                        <|> char '\\' <:> single anyChar) $ char '\"'

optSign :: CharParser st String
optSign = option "" (single $ oneOf "+-")

postDecimal :: CharParser st String
postDecimal = char '.' <:> getNumber

fullDecimal :: CharParser st String
fullDecimal = getNumber <++> option "" postDecimal

decimalLit :: CharParser st String
decimalLit = optSign <++> fullDecimal

floatingPointLit :: CharParser st String
floatingPointLit = optSign <++> (fullDecimal <|> postDecimal)
  <++> option "" (oneOf "eE" <:> optSign <++> getNumber)
  <++> single (oneOf "fF")

languageTag :: CharParser st String
languageTag = atMost1 4 letter
  <++> flat (many $ char '-' <:> atMost1 8 alphaNum)

stringConstant :: CharParser st Constant
stringConstant = do
  s <- stringLit
  do  string "^^"
      d <- datatype
      return $ Constant s $ Typed d
    <|> do
      char '@'
      t <- languageTag
      return $ Constant s $ Untyped t
    <|> return (Constant s $ Typed $ mkQName "string")

constant :: CharParser st Constant
constant = do
    f <- try floatingPointLit
    return $ Constant f $ Typed $ mkQName "float"
  <|> do
    d <- decimalLit
    return $ Constant d $ Typed $ mkQName
      $ if any (== '.') d then "decimal" else "integer"
  <|> stringConstant
