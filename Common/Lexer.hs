{-# LANGUAGE FlexibleContexts #-}
{- |
Module      :  ./Common/Lexer.hs
Description :  scanner for Casl tokens using Parsec
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Scanner for Casl tokens using Parsec <http://www.cs.uu.nl/~daan/parsec.html>
according to chapter II.4 (Lexical Symbols) of the CASL reference manual
-}

module Common.Lexer where

import Common.Id
import Common.Parsec
import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Pos as Pos

import Control.Monad
import Data.Char
import Data.List

-- * positions from "Text.ParserCombinators.Parsec.Pos" starting at (1,1)

-- | no-bracket-signs (excluding mu!)
isSignChar :: Char -> Bool
isSignChar c = if isAscii c then elem c "!#$&*+-./:<=>?@\\^|~" else
  isPunctuation c || isSymbol c || Data.Char.isNumber c

-- \172 neg \183 middle dot \215 times

-- at least two semicolons
semis :: CharParser st String
semis = tryString ";;" <++> many (char ';')

scanAnySigns :: CharParser st String
scanAnySigns =
    many1 (satisfy isSignChar <?> "casl sign") <|> semis <?> "signs"

-- | casl letters (all isAlpha including feminine and masculine ordinal and mu)
caslLetters :: Char -> Bool
caslLetters = isAlpha

-- ['A'..'Z'] ++ ['a'..'z'] ++

{- see <http://www.htmlhelp.com/reference/charset/> starting from \192
\208 ETH \215 times \222 THORN \240 eth \247 divide \254 thorn
excluded are:
\170 feminine ordinal \181 micro sign (mu) \186 masculine ordinal
 -}

caslLetter :: CharParser st Char
caslLetter = satisfy caslLetters <?> "casl letter"

scanLPD :: CharParser st Char
scanLPD = caslLetter <|> digit <|> char '\'' <?> "casl char"

-- * ParsecCombinator extension

lookaheadPosition :: String
lookaheadPosition = "lookahead position "

myLookAhead :: GenParser tok st a -> GenParser tok st a
myLookAhead parser = do
    state <- getParserState
    x <- fmap Just parser <|> return Nothing
    p <- getPosition
    _ <- setParserState state
    case x of
      Nothing -> fail $ lookaheadPosition ++ showPos
                 (fromSourcePos p) { Common.Id.sourceName = "" } ")"
      Just y -> return y

followedWith :: GenParser tok st a -> GenParser tok st b -> GenParser tok st a
followedWith p q = try $ p << myLookAhead q

checkWithUsing :: (a -> String) -> GenParser tok st a -> (a -> Bool)
          -> GenParser tok st a
checkWithUsing display p f = do
  x <- p
  if f x then return x else unexpected (display x)

checkWith :: Show a => GenParser tok st a -> (a -> Bool) -> GenParser tok st a
checkWith = checkWithUsing show

separatedBy :: GenParser tok st a -> GenParser tok st b
            -> GenParser tok st ([a], [b])
separatedBy p s = do
  r <- p
  option ([r], []) $ do
    t <- s
    (es, ts) <- separatedBy p s
    return (r : es, t : ts)

-- * casl words

scanLetterWord :: CharParser st String
scanLetterWord = caslLetter <:> many scanLPD <?> "letter word"

singleUnderline :: CharParser st Char
singleUnderline = char '_' `followedWith` scanLPD

scanUnderlineWord :: CharParser st String
scanUnderlineWord = singleUnderline <:> many1 scanLPD

scanAnyWords :: CharParser st String
scanAnyWords = flat (scanLetterWord <:> many scanUnderlineWord) <?> "words"

scanDot :: CharParser st Char
scanDot = char '.' `followedWith` caslLetter

scanDotWords :: CharParser st String
scanDotWords = scanDot <:> scanAnyWords

-- * casl escape chars for quoted chars and literal strings

-- see ParsecToken.number
value :: Int -> String -> Int
value base = foldl (\ x d -> base * x + digitToInt d) 0

digits :: Int -> Int -> Int
digits b n = if n == 0 then 0 else 1 + digits b (div n b)

valueCheck :: Int -> String -> Bool
valueCheck b s = let
  n = length s
  m = ord maxBound
  in n >= digits b 255 && n <= digits b m && value b s <= m

simpleEscape :: CharParser st String
simpleEscape = single (oneOf "'\"\\ntrvbfa?")

decEscape :: CharParser st String
decEscape = many1 digit `checkWith` valueCheck 10

hexEscape :: CharParser st String
hexEscape = char 'x' <:> many1 hexDigit `checkWith` valueCheck 16

octEscape :: CharParser st String
octEscape = char 'o' <:> many1 octDigit `checkWith` valueCheck 8

escapeChar :: CharParser st String
escapeChar = char '\\' <:>
             (simpleEscape <|> decEscape <|> hexEscape <|> octEscape)

-- * chars for quoted chars and literal strings

printable :: CharParser st String
printable = single $ satisfy $ \ c -> notElem c "'\"\\" && c > '\026'

caslChar :: CharParser st String
caslChar = escapeChar <|> printable

scanQuotedChar :: CharParser st String
scanQuotedChar = enclosedBy (caslChar <|> (char '"' >> return "\\\""))
    (char '\'') <?> "quoted char"

-- convert '"' to '\"' and "'" to "\'" (no support for ''')

scanString :: CharParser st String
scanString = flat (many (caslChar <|> (char '\'' >> return "\\\'")))
    `enclosedBy` char '"' <?> "literal string"

isString :: Token -> Bool
isString = isPrefixOf "\"" . tokStr

parseString :: CharParser () a -> String -> a
parseString p s = case parse p "" s of
                  Left _ -> error $ "parseString: " ++ s
                  Right x -> x

splitString :: CharParser () a -> String -> (a, String)
splitString p = parseString $ do
  hd <- p
  tl <- getInput
  return (hd, tl)

-- * digit, number, fraction, float

getNumber :: CharParser st String
getNumber = many1 digit

getSignedNumber :: CharParser st String
getSignedNumber = optionL (string "-") <++> getNumber

scanFloat :: CharParser st String
scanFloat = getNumber
  <++> (optionL (try $ char '.' <:> getNumber)
        <++> optionL (char 'E' <:> optionL (single $ oneOf "+-")
                        <++> getNumber))


{- | In addition to scanFloat, also '1.', '.1' and '2.e-13' are recognized
as well as preceding signs '+-'. -}
scanFloatExt :: CharParser st String
scanFloatExt =
    let -- the 'E' component
        compE = oneOf "eE" <:> getSNum
        -- the '.' component
        compD n = char '.' <:> n
        -- an optional number
        getNum' = option "0" getNumber
        checkSign' '-' = "-"
        checkSign' _ = ""
        checkSp' = (++ "0.") . checkSign' . head
        getSNum = optionL (oneOf "+-" >-> checkSign') <++> getNumber
    in -- '1.' or '2.e-13' or '1.213'
      try (getSNum <++> (optionL (try $ compD getNum') <++> optionL compE))
      -- everything starting with a dot
      <|> (choice (map string ["+.", "-.", "."]) >-> checkSp') <++> getNumber
              <++> optionL compE

scanDigit :: CharParser st String
scanDigit = single digit

isNumber :: Token -> Bool
isNumber t = case tokStr t of
  c : _ : _ -> isDigit c
  _ -> False

isFloating :: Token -> Bool
-- precondition: isNumber
isFloating = any (`elem` ".eE") . tokStr

-- * skip whitespaces and nested comment out

nestCommentOut :: CharParser st ()
nestCommentOut = forget $ nestedComment "%[" "]%"

skip :: CharParser st ()
skip = skipMany (forget (satisfy isSpace) <|> nestCommentOut <?> "")

fromSourcePos :: Pos.SourcePos -> Pos
fromSourcePos p =
    newPos (Pos.sourceName p) (Pos.sourceLine p) (Pos.sourceColumn p)

getPos :: GenParser tok st Pos
getPos = fmap fromSourcePos getPosition

-- only skip to an annotation if it's on the same or next line
skipSmart :: CharParser st ()
skipSmart = do
  p <- getPosition
  try (do
      skip
      q <- getPosition
      unless (Pos.sourceLine q <= Pos.sourceLine p + 1)
        $ notFollowedBy (char '%') >> return ())
    <|> return ()

-- * keywords WORDS or NO-BRACKET-SIGNS

keyWord :: CharParser st a -> CharParser st a
keyWord = try . (<< notFollowedBy (scanLPD <|> singleUnderline))

keySign :: CharParser st a -> CharParser st a
keySign = try . (<< notFollowedBy (satisfy isSignChar))

-- * lexical tokens with position

parseToken :: CharParser st String -> CharParser st Token
parseToken = liftM2 (\ p s -> Token s $ Range [p]) getPos

pToken :: CharParser st String -> CharParser st Token
pToken = parseToken . (<< skipSmart)

pluralKeyword :: String -> CharParser st Token
pluralKeyword s = pToken (keyWord (string s <++> optionL (string "s")))
  <?> show s

-- | check for keywords (depending on lexem class)
toKey :: String -> CharParser st String
toKey s = let p = string s in
  if last s `elem` "[]{}(),;" then p
  else if isSignChar $ last s then keySign p
       else keyWord p

-- * some separator parsers

asSeparator :: String -> CharParser st Token
asSeparator = pToken . string

commaT :: CharParser st Token
commaT = asSeparator ","

-- a single semicolon
semiT :: CharParser st Token
semiT = pToken $ string ";" << notFollowedBy (char ';')

oBraceT :: CharParser st Token
oBraceT = asSeparator "{"

cBraceT :: CharParser st Token
cBraceT = asSeparator "}"

oBracketT :: CharParser st Token
oBracketT = asSeparator "["

cBracketT :: CharParser st Token
cBracketT = (tryString "]%" >> unexpected "block-comment-end ]%" <?> "")
    <|> asSeparator "]"

oParenT :: CharParser st Token
oParenT = asSeparator "("

cParenT :: CharParser st Token
cParenT = asSeparator ")"

braces :: CharParser st a -> CharParser st a
braces p = oBraceT >> p << cBraceT

brackets :: CharParser st a -> CharParser st a
brackets p = oBracketT >> p << cBracketT

parens :: CharParser st a -> CharParser st a
parens p = oParenT >> p << cParenT

commaSep1 :: CharParser st a -> CharParser st [a]
commaSep1 p = fmap fst $ separatedBy p commaT

placeS :: CharParser st String
placeS = tryString place

placeT :: CharParser st Token
placeT = pToken placeS

{- ParsecCombinator.notFollowedBy only allows to check for a single "tok"
thus a single Char. -}

notFollowedWith :: GenParser tok st a -> GenParser tok st b
                -> GenParser tok st a
notFollowedWith p1 p2 =
  try $ join $ (try (p1 >> p2) >> return pzero) <|> return p1
{- see http://www.mail-archive.com/haskell@haskell.org/msg14388.html
by Andrew Pimlott -}
