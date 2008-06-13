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

import Data.Char (digitToInt, isDigit, ord)
import Common.Id
import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Pos as Pos

-- * positions from "Text.ParserCombinators.Parsec.Pos" starting at (1,1)

-- | no-bracket-signs
signChars :: String
signChars = "!#$&*+-./:<=>?@\\^|~" ++ -- "¡¢£§©¬°±²³µ¶·¹¿×÷"
    "\161\162\163\167\169\172\176\177\178\179\181\182\183\185\191\215\247"

-- \172 neg \183 middle dot \215 times

-- at least two semicolons
semis :: CharParser st String
semis = try (string ";;") <++> many (char ';')

scanAnySigns :: CharParser st String
scanAnySigns = fmap (\ s -> if s == "\215" then "*" else s)
    (many1 (oneOf signChars <?> "casl sign")) <|> semis <?> "signs"

-- | casl letters
caslLetters :: Char -> Bool
caslLetters ch = let c = ord ch in
   if c <= 122 && c >= 65 then  c >= 97 || c <= 90
   else c >= 192 && c <= 255 && not (elem c [215, 247])

-- ['A'..'Z'] ++ ['a'..'z'] ++
-- "ÀÁÂÃÄÅÆÇÈÉÊËÌÍÎÏÐÑÒÓÔÕÖØÙÚÛÜÝÞßàáâãäåæçèéêëìíîïðñòóôõöøùúûüýþÿ"

-- see <http://www.htmlhelp.com/reference/charset/> starting from \192
-- \208 ETH \215 times \222 THORN \240 eth \247 divide \254 thorn

caslLetter :: CharParser st Char
caslLetter = satisfy caslLetters <?> "casl letter"

prime :: CharParser st Char
prime = char '\'' -- also used for quoted chars

scanLPD :: CharParser st Char
scanLPD = caslLetter <|> digit <|> prime <?> "casl char"

-- * Monad and Functor extensions

bind :: (Monad m) => (a -> b -> c) -> m a -> m b -> m c
bind f p q = do { x <- p; y <- q; return (f x y) }

infixl <<

(<<) :: (Monad m) => m a -> m b -> m a
(<<) = bind const

infixr 5 <:>

(<:>) :: (Monad m) => m a -> m [a] -> m [a]
(<:>) = bind (:)

infixr 5 <++>

(<++>) :: (Monad m) => m [a] -> m [a] -> m [a]
(<++>) = bind (++)

-- Functor extension
single :: (Functor f, Monad m) => f a -> f (m a)
single = fmap return

flat :: (Functor f) => f [[a]] -> f [a]
flat = fmap concat

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

begDoEnd :: (Monad f, Functor f) => f a -> f [a] -> f a -> f [a]
begDoEnd open p close = open <:> p <++> single close

enclosedBy :: (Monad f, Functor f) => f [a] -> f a -> f [a]
enclosedBy p q = begDoEnd q p q

checkWith :: (Show a) => GenParser tok st a -> (a -> Bool)
          -> GenParser tok st a
checkWith p f = do
  x <- p
  if f x then return x else unexpected (show x)

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
value base s = foldl (\x d -> base*x + (digitToInt d)) 0 s

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
    prime <?> "quoted char"

-- convert '"' to '\"' and "'" to "\'" (no support for ''')

scanString :: CharParser st String
scanString = flat (many (caslChar <|> (char '\'' >> return "\\\'")))
    `enclosedBy` char '"' <?> "literal string"

isString :: Token -> Bool
isString t = take 1 (tokStr t) == "\""

parseString :: Parser a -> String -> a
parseString p s = case parse p "" s of
                  Left _ -> error $ "parseString: " ++ s
                  Right x -> x

splitString :: Parser a -> String -> (a, String)
splitString p s =
    let ph = do hd <- p;
                tl <- getInput;
                return (hd, tl)
        in parseString ph s

-- * digit, number, fraction, float

getNumber :: CharParser st String
getNumber = many1 digit

scanFloat :: CharParser st String
scanFloat = getNumber <++> (option ""
             (try $ char '.' <:> getNumber)
              <++> option ""
              (char 'E' <:> option "" (single $ oneOf "+-")
               <++> getNumber))

scanDigit :: CharParser st String
scanDigit = single digit

isNumber :: Token -> Bool
isNumber t = case tokStr t of
  c:_:_ -> isDigit c
  _     -> False

isFloating :: Token -> Bool
-- precondition: isNumber
isFloating t = any (\ c -> c == '.' || c == 'E') $ tokStr t

isLitToken :: Token -> Bool
isLitToken t = case tokStr t of
  c : _ -> c == '\"' || c == '\'' || isDigit c
  _ -> False

-- * nested comment outs

nestedComment :: String -> String -> CharParser st String
nestedComment op@(oh : ot : _) cl@(ch : ct : _) =
    try (string op) <++>
    flat (many $ single (noneOf [oh, ch]
                        <|> try (char ch << notFollowedBy (char ct))
                        <|> try (char oh << notFollowedBy (char ot))
                        ) <|> nestedComment op cl)
    <++> string cl
nestedComment _ _ = error "nestedComment"

plainBlock :: String -> String -> CharParser st String
plainBlock op cl = try (string op) >> manyTill anyChar (try $ string cl)

forget :: GenParser tok st a -> GenParser tok st ()
forget = (>> return ())

nestCommentOut :: CharParser st ()
nestCommentOut = forget $ nestedComment "%[" "]%"

-- * skip whitespaces and nested comment out

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
skipSmart = do p <- getPosition
               try (do skip
                       q <- getPosition
                       if Pos.sourceLine q <= Pos.sourceLine p + 1
                           then return ()
                           else notFollowedBy (char '%') >> return ()
                   )
                <|> return ()

-- * keywords WORDS or NO-BRACKET-SIGNS

keyWord :: CharParser st a -> CharParser st a
keyWord p = try(p << notFollowedBy (scanLPD <|> singleUnderline))

keySign :: CharParser st a -> CharParser st a
keySign p = try(p << notFollowedBy (oneOf signChars))

reserved :: [String] -> CharParser st String -> CharParser st String
-- "try" to avoid reading keywords
reserved l p = try $ checkWith p (`notElem` l)

-- * lexical tokens with position

pToken :: CharParser st String -> CharParser st Token
pToken parser =
  bind (\ p s -> Token s $ Range [p]) getPos (parser << skipSmart)

pluralKeyword :: String -> CharParser st Token
pluralKeyword s = pToken (keyWord (string s <++> option "" (string "s")))
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
cBracketT = (try (string "]%") >> unexpected "block-comment-end ]%" <?> "")
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
placeS = try (string place) <?> place

placeT :: CharParser st Token
placeT = pToken placeS

-- ParsecCombinator.notFollowedBy only allows to check for a single "tok"
-- thus a single Char.

notFollowedWith :: GenParser tok st a -> GenParser tok st b
                -> GenParser tok st a
notFollowedWith p1 p2 = try $ do
  pp <- (try (p1 >> p2) >> return pzero) <|> return p1
  pp
-- see http://www.mail-archive.com/haskell@haskell.org/msg14388.html
-- by Andrew Pimlott
