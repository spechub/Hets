{- |
Module      :  $Header$
Description :  scanner for Casl tokens using Parsec
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

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
import Data.Char (digitToInt, isDigit, ord)
import Data.List (isPrefixOf)

-- * positions from "Text.ParserCombinators.Parsec.Pos" starting at (1,1)

-- | no-bracket-signs
signChars :: String
signChars = "!#$&*+-./:<=>?@\\^|~" ++
    "\161\162\163\167\169\172\176\177\178\179\181\182\183\185\191\215\247"

-- \172 neg \183 middle dot \215 times

-- at least two semicolons
semis :: CharParser st String
semis = tryString ";;" <++> many (char ';')

scanAnySigns :: CharParser st String
scanAnySigns = fmap (\ s -> if s == "\215" then "*" else s)
    (many1 (oneOf signChars <?> "casl sign")) <|> semis <?> "signs"

-- | casl letters
caslLetters :: Char -> Bool
caslLetters ch = let c = ord ch in
   if c <= 122 && c >= 65 then  c >= 97 || c <= 90
   else c >= 192 && c <= 255 && notElem c [215, 247]

-- ['A'..'Z'] ++ ['a'..'z'] ++

-- see <http://www.htmlhelp.com/reference/charset/> starting from \192
-- \208 ETH \215 times \222 THORN \240 eth \247 divide \254 thorn

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
    setParserState state
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

simpleEscape :: CharParser st String
simpleEscape = single (oneOf "'\"\\ntrvbfa?")

decEscape :: CharParser st String
decEscape = count 3 digit `checkWith` \s -> value 10 s <= 255

hexEscape :: CharParser st String
hexEscape = char 'x' <:> count 2 hexDigit -- cannot be too big

octEscape :: CharParser st String
octEscape = char 'o' <:>
            count 3 octDigit `checkWith` \s -> value 8 s <= 255

escapeChar :: CharParser st String
escapeChar = char '\\' <:>
             (simpleEscape <|> decEscape <|> hexEscape <|> octEscape)

-- * chars for quoted chars and literal strings

printable :: CharParser st String
printable = single (satisfy (\c -> (c /= '\'')  && (c /= '"')
                              && (c /= '\\') && (c > '\026')))

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

parseString :: Parser a -> String -> a
parseString p s = case parse p "" s of
                  Left _ -> error $ "parseString: " ++ s
                  Right x -> x

splitString :: Parser a -> String -> (a, String)
splitString p = parseString $ do
  hd <- p
  tl <- getInput
  return (hd, tl)

-- * digit, number, fraction, float

getNumber :: CharParser st String
getNumber = many1 digit

scanFloat :: CharParser st String
scanFloat = getNumber
  <++> (optionL (try $ char '.' <:> getNumber)
        <++> optionL (char 'E' <:> optionL (single $ oneOf "+-")
                        <++> getNumber))

scanDigit :: CharParser st String
scanDigit = single digit

isNumber :: Token -> Bool
isNumber t = case tokStr t of
  c : _ : _ -> isDigit c
  _ -> False

isFloating :: Token -> Bool
-- precondition: isNumber
isFloating = any (flip elem ".E") . tokStr

-- * skip whitespaces and nested comment out

nestCommentOut :: CharParser st ()
nestCommentOut = forget $ nestedComment "%[" "]%"

whiteChars :: String
whiteChars = "\n\r\t\v\f \160" -- non breaking space

skip :: CharParser st ()
skip = skipMany (forget (oneOf whiteChars) <|> nestCommentOut <?> "")

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
keySign = try . (<< notFollowedBy (oneOf signChars))

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
  else if last s `elem` signChars then keySign p
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

commaSep1 :: CharParser st a -> CharParser st [a]
commaSep1 p = fmap fst $ separatedBy p commaT

placeS :: CharParser st String
placeS = tryString place <?> place

placeT :: CharParser st Token
placeT = pToken placeS

-- ParsecCombinator.notFollowedBy only allows to check for a single "tok"
-- thus a single Char.

notFollowedWith :: GenParser tok st a -> GenParser tok st b
                -> GenParser tok st a
notFollowedWith p1 p2 =
  try $ join $ (try (p1 >> p2) >> return pzero) <|> return p1
-- see http://www.mail-archive.com/haskell@haskell.org/msg14388.html
-- by Andrew Pimlott
